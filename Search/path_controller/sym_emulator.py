from z3 import *
import threading
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,REG
from utils.ctx_initer import *
from utils.tool_lib import get_jump_target
from utils.log_func import *
# 这里进行判断zf标志位
zf_list={'jz':1,'jnz':0,'ja':0,'jna':1,'jnbe':0,'jbe':1,'je':1,'jne':0,'jg':0,'jnle':0,'jle':1,'jng':1}
# 这里判断进位标志位
cf_list={'jc':1,'jnc':0,'ja':0,'jnbe':0,'jae':0,'jnb':0,'jb':1,'jnae':1,'jbe':1,'jna':1}
# 这里判断符号标志位
sf_list={'js':1,'jns':0,'jnle':0,'jge':'sf=of','jnl':'sf=of','jl':'sf!=of','jnge':'sf!=of','jle':'sf!=of','jng':'sf!=of'}
# 这里判断溢出标志位
of_list={'jo':1,'jno':0,'jg':'sf=of','jnle':'sf=of','jge':'sf=of','jnl':'sf=of','jl':'sf!=of','jnge':'sf!=of','jle':'sf!=of','jng':'sf!=of'}
# 这里做奇偶标志位的检验
pf_list={'jp':1,'jpe':0,'jnp':0,'jpo':0}

DEBUG = True


'''
    这里是否要修改一下，每经过一个结点的时候就要进行路径的收集？
    -   每到一条路径就要进行一次约束的收集
    -   每次求解时都要加入新的路径约束进去，导致没有办法进行恢复
'''
def slight_touch(last_instruction, # jxx指令
                 instruction, # 跳转后的指令
                ctx,
                new_ctx,
                new_initial_entry_point,
                new_base_addr,
                regular_choice = False, # 这里设置为True表明此时仅仅对路过的正常路径收集约束
                switch_target = None, # 这里处理jmp rax的部分
                touched = False
                ):
    '''
        每次到达一个分支会产生的一个新的候选状态
    '''

    
    if instruction.getAddress() != get_jump_target(ctx,last_instruction):
        # 如果跳转失败,那就探索跳转成功的路径
        ret = 1
    else:
        ret = 0
    
    # 这里如果是正常的路径约束收集就不需要管
    if regular_choice:
        ret = ret^1

    jmp_code = str(last_instruction).split(":")[-1].split()[0]
    flag_obj_list=[] # 该结构用于存储需要的标志位对象
    flag_not_condition_list=[]
    flag_equal_condition_list=[]
    if not touched:
        ctx.popPathConstraint()
    if jmp_code in list(zf_list.keys()):
        zf_=ctx.getRegisterAst(ctx.registers.zf)
        '''
            跳转成功：期望  结果标志位
            1 1 - 1
            1 0 - 0
            0 1 - 0
            0 0 - 1
        '''
        flag_obj_list.append([zf_,zf_list[jmp_code]])
    if jmp_code in cf_list:
        '''
            原理同上
        '''
        cf_=ctx.getRegisterAst(ctx.registers.cf)
        flag_obj_list.append([cf_,cf_list[jmp_code]])
    if jmp_code in list(sf_list.keys()):
        solv=sf_list[jmp_code]
        if type(solv) == str: # 如果这个类型为str则表明有其他条件
            sf_=ctx.getRegisterAst(ctx.registers.sf)   
            of_=ctx.getRegisterAst(ctx.registers.of) 
            if '!' in solv and ret == 1: # 此时出现的是sf!=of,且允许跳转成功,跳转不成功的情况也要考虑进去
                flag_not_condition_list.append(sf_)
                flag_not_condition_list.append(of_)
            else: # 此时出现的是sf=of
                flag_equal_condition_list.append(sf_)
                flag_equal_condition_list.append(of_)
        else: # 否则与上面操作相同
            sf_=ctx.getRegisterAst(ctx.registers.sf)
            flag_obj_list.append([sf_,sf_list[jmp_code]])
    # 处理of标志位
    if jmp_code in list(of_list.keys()):
        solv=of_list[jmp_code]
        if type(solv) == str: # 如果这个类型为str则表明有其他条件
            sf_=ctx.getRegisterAst(ctx.registers.sf)   
            of_=ctx.getRegisterAst(ctx.registers.of) 
            if '!' in solv: # 此时出现的是sf!=of
                flag_not_condition_list.append(sf_)
                flag_not_condition_list.append(of_)
            else: # 此时出现的是sf=of
                flag_equal_condition_list.append(sf_)
                flag_equal_condition_list.append(of_)
        else: # 否则与上面操作相同
            of_=ctx.getRegisterAst(ctx.registers.of)
            flag_obj_list.append([of_,of_list[jmp_code]])
    # 处理pf标志位
    if jmp_code in list(pf_list.keys()):
        pf_=ctx.getRegisterAst(ctx.registers.pf)
        flag_obj_list.append([pf_,pf_list[jmp_code]])
    if jmp_code in ['jbe','jng','jna','jg']:
        '''
            二者是或运算，
        '''
        obj_list = flag_obj_list[0]
        reg_flag=obj_list[0]
        flag_val=obj_list[1]
        if len(flag_not_condition_list) !=0:
            '''
                表明是jng，zf=1或者sf!=of
            '''
            # 这里完成对条件约束的收集
            if  ret == 1:
                ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]) or (reg_flag == flag_val))
            else:
                ctx.pushPathConstraint(not ((flag_not_condition_list[0] != flag_not_condition_list[1]) or (reg_flag == flag_val)))
        elif len(flag_equal_condition_list) !=0:
            if ret ==  1:
                ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]) or (reg_flag == flag_val))
            else:
                ctx.pushPathConstraint(not (flag_equal_condition_list[0] == flag_equal_condition_list[1]) or (reg_flag == flag_val))
        else:
            '''
                表明是两个标志位的或运算
            '''
            obj_list = flag_obj_list[1]
            reg_flag_2=obj_list[0]
            flag_val_2=obj_list[1]
            # 施加or约束
            if ret == 1:
                ctx.pushPathConstraint((reg_flag_2 == flag_val_2) or (reg_flag == flag_val))
            else:
                ctx.pushPathConstraint(reg_flag_2 != flag_val_2)
                ctx.pushPathConstraint(reg_flag != flag_val)
    elif jmp_code in ['ja','jle','jnbe','jnle']:
        '''
            二者是且运算
        '''
        if len(flag_not_condition_list) !=0:
            '''
                ZF=1 和 SF!=OF
            '''
            obj_list = flag_obj_list[0]
            reg_flag=obj_list[0]
            flag_val=obj_list[1]
            # 这里完成对条件约束的收集
            if ret == 1:
                ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]) and (reg_flag == flag_val))
            else:
                ctx.pushPathConstraint(not (flag_not_condition_list[0] != flag_not_condition_list[1]) and (reg_flag == flag_val))
        elif len(flag_equal_condition_list)!=0:
            '''
                ZF=0 和 SF=OF
            '''
            obj_list = flag_obj_list[0]
            reg_flag=obj_list[0]
            flag_val=obj_list[1]
            # 这里完成对条件约束的收集
            if ret ==  1:
                ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]) and (reg_flag == flag_val))
            else:
                ctx.pushPathConstraint(not (flag_equal_condition_list[0] == flag_equal_condition_list[1]) and (reg_flag == flag_val))
        else:
            '''
                两个标志位的条件
            '''
            obj_list = flag_obj_list[0]
            reg_flag=obj_list[0]
            flag_val=obj_list[1]
            obj_list = flag_obj_list[1]
            reg_flag_2=obj_list[0]
            flag_val_2=obj_list[1]
            # 施加or约束
            if ret == 1:
                ctx.pushPathConstraint((reg_flag_2 == flag_val_2))
                ctx.pushPathConstraint((reg_flag == flag_val))
            else:
                # ctx.pushPathConstraint((not ((reg_flag_2 == flag_val_2) and (reg_flag == flag_val))))
                ctx.pushPathConstraint(((reg_flag_2 != flag_val_2) or (reg_flag != flag_val)))
    elif jmp_code == 'jmp':
        if switch_target is None:
            raise Exception("No Switch Target Found!")
        astCtxt = ctx.getAstContext()
        rax   = ctx.getSymbolicRegister(ctx.registers.rax)
        rax   = astCtxt.extract(63, 0, rax.getAst())
        print(str(last_instruction.getOperands()[-1]).split(':')[0])
        ctx.pushPathConstraint(rax == switch_target)
        
    else:
        '''
            下面是直接处理一个条件的部分
        '''
        if len(flag_equal_condition_list)!=0:
            '''
                相等条件sf=of
            '''
            if ret == 1:
                ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]))
            else:
                ctx.pushPathConstraint(not ((flag_equal_condition_list[0] == flag_equal_condition_list[1])))
        elif len(flag_not_condition_list) !=0:
            '''
                不等条件
            '''
            if ret == 1:
                ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]))
            else:
                ctx.pushPathConstraint(not ((flag_not_condition_list[0] != flag_not_condition_list[1])))
        else:
            '''
                单纯符号条件
            '''
            obj_list = flag_obj_list[0]
            reg_flag=obj_list[0]
            flag_val=obj_list[1]
            if ret == 1:
                ctx.pushPathConstraint(reg_flag == flag_val)
            else:
                ctx.pushPathConstraint(reg_flag != flag_val)
    if regular_choice is not True:
        # 设置完成约束之后进行求解
        model = ctx.getModel(ctx.getPathPredicate())
        # 该变量保证程序此时有解的状态
        check_flag = 0
        # 这里创建一个新的ctx上下文进行下一次的运行
        for k, v in sorted(model.items()):
            check_flag += 1 
            new_ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())
        
        my_Cst  = ctx.getPathConstraints()
        ctx.popPathConstraint()
        # 重新收回限制
        '''
            打印debug信息
        '''
        if check_flag != 0:
            # 设置完新的初始状态后，将新的上下文进行返回
            return new_ctx
        else:
            # 删除创建的新变量
            del new_ctx
            return None
    
    my_Cst  = ctx.getPathConstraints()
    for cst in my_Cst:
        print("Comment:",cst.getComment())
        # print(cst.getTakenAddress())
        print("TakenPredicate",cst.getTakenPredicate())
    # 这里表明当前仅仅进行路径的约束收集
    return 1

# 接收当前指令即可
def slight_slight_touch(instruction, # 跳转后的指令
                        ctx,
                        new_ctx,
                        next_op = None,
                        switch_target = None,
                        ctx_list=[]):
    '''
        因此每次只需要读取一条当前指令即可，cmp指令并不会产生新的约束，jmp rax的约束弹出再放回即可
        其他约束提前给出即可
    '''
    if 'cmp' in str(instruction):
        astCtxt = ctx.getAstContext()
        # all_operands = instruction.getOperands()
        # print(instruction.getOperands()[0])
        '''
            左右两个操作数都有可能是内存操作数或者寄存器，左边一般只能是寄存器
        '''
        if instruction.getOperands()[0].getType() == OPERAND.REG:
            left_value = ctx.getConcreteRegisterValue(instruction.getOperands()[0])
            left_op = ctx.getSymbolicRegister(instruction.getOperands()[0])
            left_op = astCtxt.extract(instruction.getOperands()[-1].getBitSize()-1, 0, left_op.getAst())
            
        elif instruction.getOperands()[0].getType() == OPERAND.MEM:
            left_value = instruction.getOperands()[0].getLeaAst()
            left_op = ctx.getMemoryAst(MemoryAccess(instruction.getOperands()[0].getAddress(), instruction.getOperands()[0].getBitSize()))
            left_op   = astCtxt.extract(instruction.getOperands()[0].getBitSize()-1, 0, left_op)

          
        if instruction.getOperands()[-1].getType() == OPERAND.REG:
            '''
                寄存器的情况
            '''
            right_op   = ctx.getSymbolicRegister(instruction.getOperands()[-1])
            right_op    = astCtxt.extract(instruction.getOperands()[-1].getBitSize()-1, 0, right_op.getAst())
            right_value = ctx.getConcreteRegisterValue(instruction.getOperands()[-1])
        elif instruction.getOperands()[-1].getType() == OPERAND.MEM:
            right_value = instruction.getOperands()[-1].getLeaAst()
            right_op = ctx.getMemoryAst(MemoryAccess(instruction.getOperands()[-1].getAddress(), instruction.getOperands()[-1].getBitSize()))
            right_op   = astCtxt.extract(instruction.getOperands()[-1].getBitSize()-1, 0, right_op)
        else:
            # 这里证明是立即数
            right_value = instruction.getOperands()[-1].getValue()
            # 这里没有办法只能让二者相等
            right_op = right_value
        
        # putConstrain(ctx)
        # 检查当前op操作
        if next_op in ['jz','je','jnz','jne']:
            # 直接比较二者是否相同的指令，直接将不同的指令压入
            if left_value == right_value:
                ctx.pushPathConstraint(left_op != right_op)
            else:
                ctx.pushPathConstraint(left_op == right_op)
        elif next_op in ['jle','jbe','jna']: # 小于等于
            if left_value <= right_value:
                ctx.pushPathConstraint(left_op > right_op)
            else:
                ctx.pushPathConstraint(left_op <= right_op)
        elif next_op in ['jge','jae','jnb','jnc']: # 大于等于
            if left_value >= right_value:
                ctx.pushPathConstraint(left_op < right_op)
            else:
                ctx.pushPathConstraint(left_op >= right_op)
        elif next_op in ['jnge','jl','jb','jc','jnl']: # 小于
            if left_value < right_value:
                ctx.pushPathConstraint(left_op >= right_op)
            else:
                ctx.pushPathConstraint(left_op < right_op)
        elif next_op in ['jnle','jg','ja']: # 大于
            if left_value > right_value:
                ctx.pushPathConstraint(left_op <= right_op)
            else:
                ctx.pushPathConstraint(left_op > right_op)
        model = ctx.getModel(ctx.getPathPredicate())
        # 这里创建一个新的ctx上下文进行下一次的运行
        for k, v in sorted(model.items()):
            try:
                new_ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())
            except:
                # 这里表明有些东西在当前代码的AST树中并不存在因此可以判定为无解
                model = {}
                break

        # putConstrain(ctx)
        '''
            最后一步添加完约束，弹出约束条件
        '''
        ctx.popPathConstraint()
        '''
            判断是否有解
        '''
        if len(model) != 0:
            return new_ctx
        else:
            del new_ctx
            return None
        
    elif 'test' in str(instruction):
        if next_op in ['jz','jnz','je','jne']: # 如果该指令操作判断zf是否为0
            left_value = ctx.getConcreteRegisterValue(instruction.getOperands()[0])
            # 获取右边的符号条件
            try:
                right_value = instruction.getOperands()[-1].getValue()
            except:
                right_value = ctx.getConcreteRegisterValue(instruction.getOperands()[-1])
            astCtxt = ctx.getAstContext()
            left_op = ctx.getSymbolicRegister(instruction.getOperands()[0])
            try:
                left_op = astCtxt.extract(instruction.getOperands()[0].getBitsize()-1, 0, left_op .getAst())
            except:
                pass
            if left_value & right_value == 0:
                ctx.pushPathConstraint(not (left_op & right_value == 0))
            else:
                try:
                    ctx.pushPathConstraint(left_value & right_value == 0)
                    ctx.pushPathConstraint(left_value & right_value == 0)
                except:
                    right_op = ctx.getSymbolicRegister(instruction.getOperands()[-1])
                    ctx.pushPathConstraint(right_op == right_op )
            # 进行运算的求解
            model = ctx.getModel(ctx.getPathPredicate())
            for k, v in sorted(model.items()):
                new_ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())
            ctx.popPathConstraint()
            if len(model) != 0:
                return new_ctx
            else:
                del new_ctx
                return None
        else:
            # 此处不是新增添一个分支，无需进行处理
            return None
    # 操作switch
    elif 'jmp' in str(instruction):
        switch_target.remove(ctx.getConcreteRegisterValue(instruction.getOperands()[-1]))
        ctx.popPathConstraint()
        ctx_result_list = [] # 这里用于存储多个状态结果
        model = ctx.getModel(ctx.getPathPredicate())
        assert len(model) != 0
        for per_ctx, per_target in zip(ctx_list,switch_target):
            for k, v in sorted(model.items()):
                try:
                    per_ctx.setConcreteVariableValue(ctx.getSymbolicVariable(v.getId()), v.getValue())
                    ctx_result_list.append(per_ctx)
                except:
                    pass
        return ctx_result_list
        
class per_path_contatiner():
    def __init__(self) -> None:
        self.addr_list=[] # 用于存放跳转地址序列
        self.choice_list=[] # 用于存放到各个地址的后的选择
        self.target_addr=[] # 用于存放探索的目的地址
        self.exit_addr=[] # 用于存放探索结束的地址
        self.node_point=0
        self.searched_addr=[]
        self.addr_to_inst={}
        self.searched_choice=[]
    # 刷新路径约束便于下次探索
    def fresh(self):
        pass
    # 添加探索目标地址
    def add_target_addr(self,target_addr):
        if type(target_addr) == list:
            self.target_addr+=target_addr
        else:
            self.target_addr.append(target_addr)

    def add_exit_point(self,exit_addr):
        if type(exit_addr) == list:
            self.exit_addr+=exit_addr
        else:
                self.exit_addr.append(exit_addr)

    def add_new_node(self,new_addr,new_choice,addr_to_inst):
        # 保证函数选项是0或1
        
        if type(new_addr) == list:
            self.addr_list+=new_addr
        else:
            self.addr_list.append(new_addr)
        if type(new_choice) == list:

            self.choice_list+=new_choice
        else:
            assert new_choice == 1 or new_choice == 0
            self.choice_list.append(new_choice)
        self.addr_to_inst=addr_to_inst
    
    def is_current_equal(self,outs_addr):# 该函数用于管理路径探索时的进程
        if outs_addr not in self.addr_list:
            return False
        return True

    def touch_a_node(self,instruction,ctx): # 此处确定是到达了一个预设的节点，则弹出一部分
        address = instruction.getAddress()
        assert len(self.choice_list)!= 0 and len(self.addr_list) !=0
        '''
            这里到达一个位置后没有进行取出结点的操作
        '''
        pos=self.addr_list.index(address)
        ret=self.choice_list[pos]
        # 删除对应的选择，防止多次探索
        del self.choice_list[pos]
        del self.addr_list[pos]

        # 防止循环路径使用第一个点多次
        if len(ret) != 1:
            ret = ret.pop(0)
        else:
            ret = ret[0]
        # 这里选择的是下一条指令的地址
        next_pc = None
        # 该位置用于取出jxx指令
        c_inst=list(self.addr_to_inst[pos].keys())[0] # 这里取出对应的指令
        # 这里对应的jmp也要进行删除
        del self.addr_to_inst[pos]

        if not instruction.isSymbolized():
            return ctx, None
        
        # 这里要写一个对照表，不同的跳转指令需要的标志位是不同的
        jmp_code=str(c_inst).split(":")[-1].split()[0]
        flag_obj_list=[] # 该结构用于存储需要的标志位对象
        flag_not_condition_list=[]
        flag_equal_condition_list=[]
        if jmp_code in list(zf_list.keys()):
            zf_=ctx.getRegisterAst(ctx.registers.zf)
            '''
                跳转成功：期望  结果标志位
                1 1 - 1
                1 0 - 0
                0 1 - 0
                0 0 - 1
            '''
            flag_obj_list.append([zf_,zf_list[jmp_code]])
        if jmp_code in cf_list:
            '''
                原理同上
            '''
            cf_=ctx.getRegisterAst(ctx.registers.cf)
            flag_obj_list.append([cf_,cf_list[jmp_code]])
        if jmp_code in list(sf_list.keys()):
            solv=sf_list[jmp_code]
            if type(solv) == str: # 如果这个类型为str则表明有其他条件
                sf_=ctx.getRegisterAst(ctx.registers.sf)   
                of_=ctx.getRegisterAst(ctx.registers.of) 
                if '!' in solv and ret == 1: # 此时出现的是sf!=of,且允许跳转成功,跳转不成功的情况也要考虑进去
                    flag_not_condition_list.append(sf_)
                    flag_not_condition_list.append(of_)
                else: # 此时出现的是sf=of
                    flag_equal_condition_list.append(sf_)
                    flag_equal_condition_list.append(of_)
            else: # 否则与上面操作相同
                sf_=ctx.getRegisterAst(ctx.registers.sf)
                flag_obj_list.append([sf_,sf_list[jmp_code]])
        # 处理of标志位
        if jmp_code in list(of_list.keys()):
            solv=of_list[jmp_code]
            if type(solv) == str: # 如果这个类型为str则表明有其他条件
                sf_=ctx.getRegisterAst(ctx.registers.sf)   
                of_=ctx.getRegisterAst(ctx.registers.of) 
                if '!' in solv: # 此时出现的是sf!=of
                    flag_not_condition_list.append(sf_)
                    flag_not_condition_list.append(of_)
                else: # 此时出现的是sf=of
                    flag_equal_condition_list.append(sf_)
                    flag_equal_condition_list.append(of_)
            else: # 否则与上面操作相同
                of_=ctx.getRegisterAst(ctx.registers.of)
                flag_obj_list.append([of_,of_list[jmp_code]])
        # 处理pf标志位
        if jmp_code in list(pf_list.keys()):
            pf_=ctx.getRegisterAst(ctx.registers.pf)
            '''
                跳转成功：期望  结果标志位
                1 1 - 1
                1 0 - 0
                0 1 - 0
                0 0 - 1
            '''
            flag_obj_list.append([pf_,pf_list[jmp_code]])
        # 返回的是{obj标志：取值}
        # 这里开始根据跳转指令的不同，进行不同的施加约束操作
        if jmp_code in ['jbe','jng','jna','jg']:
            '''
                二者是或运算，
            '''
            obj_list = flag_obj_list[0]
            reg_flag=obj_list[0]
            flag_val=obj_list[1]
            if len(flag_not_condition_list) !=0:
                '''
                    表明是jng，zf=1或者sf!=of
                '''
                # 这里完成对条件约束的收集
                if  ret == 1:
                    ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]) or (reg_flag == flag_val))
                else:
                    ctx.pushPathConstraint(not ((flag_not_condition_list[0] != flag_not_condition_list[1]) or (reg_flag == flag_val)))
            elif len(flag_equal_condition_list) !=0:
                if ret ==  1:
                    ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]) or (reg_flag == flag_val))
                else:
                    ctx.pushPathConstraint(not (flag_equal_condition_list[0] == flag_equal_condition_list[1]) or (reg_flag == flag_val))
            else:
                '''
                    表明是两个标志位的或运算
                '''
                obj_list = flag_obj_list[1]
                reg_flag_2=obj_list[0]
                flag_val_2=obj_list[1]
                # 施加or约束
                if ret == 1:
                    ctx.pushPathConstraint((reg_flag_2 == flag_val_2) or (reg_flag == flag_val))
                else:
                    ctx.pushPathConstraint(reg_flag_2 != flag_val_2)
                    ctx.pushPathConstraint(reg_flag != flag_val)
        elif jmp_code in ['ja','jle','jnbe','jnle']:
            '''
                二者是且运算
            '''
            if len(flag_not_condition_list) !=0:
                '''
                    ZF=1 和 SF!=OF
                '''
                obj_list = flag_obj_list[0]
                reg_flag=obj_list[0]
                flag_val=obj_list[1]
                # 这里完成对条件约束的收集
                if ret == 1:
                    ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]) and (reg_flag == flag_val))
                else:
                    ctx.pushPathConstraint(not (flag_not_condition_list[0] != flag_not_condition_list[1]) and (reg_flag == flag_val))
            elif len(flag_equal_condition_list)!=0:
                '''
                    ZF=0 和 SF=OF
                '''
                obj_list = flag_obj_list[0]
                reg_flag=obj_list[0]
                flag_val=obj_list[1]
                # 这里完成对条件约束的收集
                if ret ==  1:
                    ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]) and (reg_flag == flag_val))
                else:
                    ctx.pushPathConstraint(not (flag_equal_condition_list[0] == flag_equal_condition_list[1]) and (reg_flag == flag_val))
            else:
                '''
                    两个标志位的条件
                '''
                obj_list = flag_obj_list[0]
                reg_flag=obj_list[0]
                flag_val=obj_list[1]
                obj_list = flag_obj_list[1]
                reg_flag_2=obj_list[0]
                flag_val_2=obj_list[1]
                # 施加or约束
                if ret == 1:
                    ctx.pushPathConstraint((reg_flag_2 == flag_val_2) and (reg_flag == flag_val))
                else:
                    # ctx.pushPathConstraint(not ((reg_flag_2 == flag_val_2) and (reg_flag == flag_val)))
                    ctx.pushPathConstraint(((reg_flag_2 != flag_val_2) or (reg_flag != flag_val) or ((reg_flag_2 != flag_val_2) and (reg_flag != flag_val) )))
        elif jmp_code == 'jmp':
            '''
                这里处理Switch的情况
            '''
            next_pc = ret # 这里获取下一跳的地址
        else:
            '''
                下面是直接处理一个条件的部分
            '''
            if len(flag_equal_condition_list)!=0:
                '''
                    相等条件sf=of
                '''
                if ret == 1:
                    ctx.pushPathConstraint((flag_equal_condition_list[0] == flag_equal_condition_list[1]))
                else:
                    ctx.pushPathConstraint(not ((flag_equal_condition_list[0] == flag_equal_condition_list[1])))
            elif len(flag_not_condition_list) !=0:
                '''
                    不等条件
                '''
                if ret == 1:
                    ctx.pushPathConstraint((flag_not_condition_list[0] != flag_not_condition_list[1]))
                else:
                    ctx.pushPathConstraint(not ((flag_not_condition_list[0] != flag_not_condition_list[1])))
            else:
                '''
                    单纯符号条件
                '''
                obj_list = flag_obj_list[0]
                reg_flag=obj_list[0]
                flag_val=obj_list[1]
                if ret == 1:
                    ctx.pushPathConstraint(reg_flag == flag_val)
                else:
                    ctx.pushPathConstraint(reg_flag != flag_val)
        # 这里直接返回施加完约束的上下文xpects an AstNode as first argument.
        return ctx, next_pc

        
class path_emulator(threading.Thread):
    
    def __init__(self,
        thread_id, # 给当前的线程一个id便于操作
        context,
        start_address, # 开始执行的位置
        lib_gst_code_seg,
        path_model:per_path_contatiner, # 用于才存放路径对象
        taint_mem_dcit = None, # 该参数用于记录需要污染的内存
        base_addr = None
    ) -> None:
        super(path_emulator, self).__init__()
        self.base_addr = base_addr
        self.thread_id=thread_id
        self.ctx=context
        self.entry_point=start_address
        self.result=None # 该位置用于存储多线程的返回值
        self.path_model=path_model
        self.result=None
        # 设定污染内存和污染指令地址
        self.taint_addr=[]
        self.taint_mem_dcit = taint_mem_dcit # 该参数用于记录需要污染的内存
        self.taint_mem={} # {目标地址：目标长度}
        # 下面用于符号执行的部分
        self.instruct_queue =[]
        self.lib_gst_code_seg = lib_gst_code_seg
        self.cycle_mode = None # 这里等待添加循环控制部分
        #该数据结构用于记录一个受污染的指令是否被执行太多次
        self.taint_record={} # 

    # 该函数的作用是设定符号化地址，对指令产生的影响进行符号化
    def add_symbol_inst_addr(self,tainted_address):
        if type(tainted_address) is list:
            self.taint_addr+=tainted_address
        else:
            self.taint_addr.append(tainted_address)

    # 该函数的作用是设定符号化内存，对某些内存设定为符号值
    def add_symbol_mem(self,target_addr:int,mem_len:int): # 第一个参数标记内存位置，第二个标记标注内存的长度
        self.taint_mem[target_addr]=mem_len
    
    def check_repeat_instruct(self):
        str_inst = [str(inst) for inst in self.instruct_queue]
        if (len(set(str_inst)) != len(self.instruct_queue) and len(set(str_inst))==1):
            return True
        return False
    def push_queue_ram(self,inst):
        if len(self.instruct_queue) >= 10:
            self.instruct_queue.pop(0)
        self.instruct_queue.append(inst)

    def add_cycle_mode(self,cycle_mode):                
        self.cycle_mode = cycle_mode
    def run(self):
        '''
            污点分析部分
            这里做一点要求，预先设定的内存位置不要与后面代码操作中的设定出现冲突
        '''
        if len(self.taint_mem) != 0:
            for t_mem in self.taint_mem:
                mem_len=self.taint_mem[t_mem]
                self.ctx.taintMemory(MemoryAccess(t_mem,re_align(mem_len)))
                self.ctx.symbolizeMemory(MemoryAccess(t_mem,re_align(mem_len)))

        print("\033[92m" + "Starting Symbolic Engine ..... " + "\033[0m")
        inst_counter = 0
        for i in range(1):
            pc = self.entry_point
            # 做一个刷新操作

            # TODO(ctx fresh的代码也得用
            '''
                如果需要多次运行同一段代码，这里需要加入对上下文重置的代码
            '''
            exit_count = 0 # 该变量用于记录当前程序中应该多少次退出
            last_loop_flag = 0
            while pc:
                opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16) # 这里是取出其中的操作码
                instruction = Instruction(pc, opcode)   
                self.ctx.processing(instruction)
                # 用于跳出循环的操作
                pre_pc = instruction.getNextAddress()
                next_pc = None
                if DEBUG:
                    if instruction.isSymbolized():
                        print("\033[92m" + str(instruction) + "\033[0m")
                    else:
                        print(instruction)
                inst_counter += 1
                if instruction.getAddress() in self.taint_addr:# 此处需要进行符号化的指令
                    if str(instruction).split(":")[-1].split()[0] == 'call':
                        self.last_call_taint=True # 这里表明有可能是进行库函数调用
                    else:
                        target_tainted,taint_type=get_target_oprand(instruction)
                        if taint_type == 1: # 这个位置开始进行内存的污染
                            self.ctx.taintMemory(target_tainted)
                        elif taint_type == 0 : # 这个位置开始进行寄存器的污染
                            self.ctx.taintRegister(target_tainted)
                            self.ctx.symbolizeRegister(target_tainted) # 对寄存器进行符号化的操作

                # 关键跳转所在位置，也是需要收集路径约束的位置
                if instruction.getNextAddress() in self.path_model.addr_list: # 这里的addr_list
                    # 触及到之后就清除节点，这里的next pc是用于处理jmp rax这种情况的
                    self.ctx,next_pc=self.path_model.touch_a_node(instruction,self.ctx)
                    model = self.ctx.getModel(self.ctx.getPathPredicate())
                    for k, v in sorted(model.items()):
                        self.ctx.setConcreteVariableValue(self.ctx.getSymbolicVariable(v.getId()), v.getValue())

                # 运行目标地址
                if len(self.path_model.addr_list) == 0 or  not (pc < self.lib_gst_code_seg['start'] + self.lib_gst_code_seg['size'] and pc >self.lib_gst_code_seg['start']):
                    exit_count += 1
                    if exit_count > 2:
                        model = self.ctx.getModel(self.ctx.getPathPredicate()) # 这里的获取模型其实就是
                        if not model:
                            print('[-] Failed untouchable path found')
                            self.result =  None
                            return 
                        for k, v in sorted(model.items()):
                            # 将先前的符号值设置为具体值
                            self.ctx.setConcreteVariableValue(self.ctx.getSymbolicVariable(v.getId()), v.getValue())
                        break

                self.ctx=hookingHandler(self.ctx)
                # 这里用来处理循环结构
                ret_val,loop_flag = self.cycle_mode.search_cycle(instruction,None,self.base_addr)

                if len(self.instruct_queue) != 0:
                    if self.instruct_queue[-1].getAddress() in self.taint_record and \
                        self.taint_record[self.instruct_queue[-1].getAddress()]==0: # 如果上条跳转指令的部分并没有被记录进去，则本条就是其目的地址
                        self.taint_record[self.instruct_queue[-1].getAddress()]=instruction.getAddress() # 当前就是上一次的答案

                if instruction.isBranch():
                    jump_tartget=get_jump_target(self.ctx,instruction)
                    # tmp_address=str(instruction).split(":")[0]
                    if last_loop_flag == -1: # 此处可以进行强制的跳出
                        print("loop too much!now break")
                        if int(jump_tartget,16) == self.taint_record[instruction.getAddress()]: # 以前都是跳转成功，那么这次就让他跳转失败
                            pc = pre_pc # 直接进入下一条
                        else:
                            pc = int(jump_tartget,16) # 以前跳转都是失败，这次就让他跳转成功
                    elif last_loop_flag == 2: # 当前进入了一次新的循环，但是并不需要被跳转
                        # 本次跳转做出的抉择需要被记录
                        assert instruction.getAddress() in self.taint_record
                        # self.taint_record[instruction.getAddress()]=0
                    elif last_loop_flag == 1: # 自然退出，如果属于的话就继续
                        del self.taint_record[instruction.getAddress()]

                    elif last_loop_flag == 0:
                        # 如果是当前新进入的一个循环就创建其对应的循环控制结构
                        self.taint_record[instruction.getAddress()]=0
                        last_loop_flag=loop_flag



                self.push_queue_ram(inst=instruction)
                # 程序结束位置
                if instruction.getType() == OPCODE.X86.HLT or instruction.getAddress() in self.path_model.exit_addr or self.check_repeat_instruct():
                    break
                if inst_counter > 10000:
                    break
                if ANALYSE_MODE is X86_32:
                    pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
                else:
                    pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
                if next_pc is not None:
                    pc = next_pc # 这里遇到jmp rax，能够进行获取下一跳的地址
        # 这里解出来的是小段序列的解

        result={}
        mem_map=self.ctx.getSymbolicMemory()
        for j in mem_map:
            # print(chr(self.ctx.getSymbolicMemoryValue(MemoryAccess(j,CPUSIZE.BYTE))),end='')
            result[j]=self.ctx.getSymbolicMemoryValue(MemoryAccess(j,CPUSIZE.BYTE))
        self.result=result

    # 运行结果是      
    def get_result(self):
        return self.result
