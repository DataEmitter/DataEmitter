import  angr
import os
from triton import OPERAND
from copy import deepcopy
from triton import *
from  utils.tool_lib import get_jump_target
from config.__config import *
from triton import ARCH
DEBUG=False
# 每次遇到一个Switch节点就进行
class switch_mode():
    def __init__(self) -> None:
        pass

# 用于进行路径的探索和
class path_solver():
    def __init__(self,bin_path,code_base,angr_proj = None,
                 cfg_model=None,loop_list =None) -> None:
        if angr_proj is None:
            if ANALYSE_MODE == 1: # 64w为分析
                angr_proj=angr.Project(bin_path, arch='x86_64',auto_load_libs=False)
            else:
                angr_proj=angr.Project(bin_path, arch='x86',auto_load_libs=False)
        else:
            angr_proj = angr_proj
        if cfg_model is None:
            self.cfg = angr_proj.analyses.CFGFast()
        else:
            self.cfg = cfg_model
        
        self.switch_nodes = {}
        self.code_base = code_base
        for node in self.cfg.nodes():
            if len(node.successors) > 2:
                if node.block is not None:
                    self.switch_nodes[node.block.instruction_addrs[-1]-ANGR_BASE + code_base] = node
                else:
                    self.switch_nodes[node.addr -ANGR_BASE + code_base] = node
        # 记录分支节点
        self.last_instruct = None
        self.last_cmp = None # 用于缓存cmp指令
        self.last_jxx = None # 用于缓存jxx指令
        self.jmp_path = []
        self.cmp_path = []
        # 以下两个变量用于存储新产生的路径
        self.new_jmp_path = []  # [{},{},{}]
        self.new_cmp_path = []
        self.main_jmp_path = [] # 该结构用于记录本次执行的路径
        self.main_cmp_path = []
        # 以下两个变量用于实现对于gadget路径的记录
        self.real_main_cmp_path = []
        self.real_main_jmp_path = []   
        self.state_gdt_jmp_path = None
        self.state_gdt_cmp_path = None
        self.fake_jmp_path = None
        self.fake_cmp_path = None
        # 该变量用于记录本次新生成的路径
        self.current_new_cmp = list()
        self.current_new_jmp = list()
    
    def clear(self):
        # 记录分支节点,重新记录当前分支中的内容
        self.last_instruct = None
        self.last_last_instruction = None
        self.last_cmp = None # 用于缓存cmp指令
        self.last_jxx = None # 用于缓存jxx指令
        self.jmp_path = []
        self.cmp_path = []
        # 以下两个变量用于存储新产生的路径
        self.new_jmp_path = []  # [{},{},{}]
        self.new_cmp_path = []
        self.main_jmp_path = [] # 该结构用于记录本次执行的路径
        self.main_cmp_path = [] # 记录本次cmp路径
        # 以下两个变量用于实现对于gadget路径的记录
        self.real_main_cmp_path = []
        self.real_main_jmp_path = []   
        # 以下用于记录分支节点的污染情况
        self.taint_state_table = []
        # 重新写入固定路径
        self.fake_jmp_path = deepcopy(self.state_gdt_jmp_path)
        self.fake_cmp_path = deepcopy(self.state_gdt_cmp_path)
        self.new_cmp_path = [deepcopy(self.state_gdt_cmp_path)]
        self.new_jmp_path = [deepcopy(self.state_gdt_jmp_path)]

    def getSwitchMode(self,instruction):
        switch_target = []
        for next_block in self.switch_nodes[instruction.getAddress()].successors:
            switch_target.append(next_block.addr - ANGR_BASE + self.code_base)
        return switch_target

    def set_state_path(self,state_gdt_jmp_path , state_gdt_cmp_path):
        self.state_gdt_jmp_path = state_gdt_jmp_path
        self.state_gdt_cmp_path = state_gdt_cmp_path 
        self.fake_jmp_path = deepcopy(state_gdt_jmp_path)
        self.fake_cmp_path = deepcopy(state_gdt_cmp_path)
        self.new_cmp_path=[deepcopy(state_gdt_cmp_path)]
        self.new_jmp_path=[deepcopy(state_gdt_jmp_path)]

    # 传入的第三个参数是新的gadget mode模型
    def solve(self,instruction,ctx,hooking_flag, new_gadget,new_gdt_list = []):
        # 第二种情况剔除了jmp 固定地址的情况
        if not instruction.isBranch() or ('jmp' in str(instruction) and instruction.getOperands()[0].getType() != OPERAND.REG):
            # 对于非分支的部分不做任何处理
            if 'cmp' in str(instruction) or 'test' in str(instruction):
                '''
                    hook cmp的情况
                '''
                self.last_cmp = instruction
            elif self.last_jxx is not None and self.last_cmp is not None and (self.last_instruct.getAddress() == self.last_jxx.getAddress()):
                # 此处检查新的分支语句,这里将str转化为数字,表明跳转成功
                try:
                    target_jmpadr = int(get_jump_target(ctx,self.last_jxx),16)
                except:
                    # 这里证明是获取一个跳转寄存器
                    target_jmpadr = ctx.getConcreteRegisterValue(ctx.getRegister(get_jump_target(ctx,self.last_jxx)))
                if target_jmpadr == instruction.getAddress():
                    jmp_flag = True
                else:
                    jmp_flag = False
                # 记录新路径
                self.jmp_path.append({self.last_jxx:jmp_flag})
                self.cmp_path.append({self.last_cmp:jmp_flag})
                self.generate_new_path(jmp_flag)
                # 清空旧的缓存
                self.last_cmp = None
                self.last_jxx = None
            elif self.last_instruct is not None:
                if self.last_instruct.getAddress() in self.switch_nodes and 'ret' not in str(self.last_instruct)and 'jmp' not in str(self.last_instruct):
                    if self.jmp_path[-1][self.last_instruct.getAddress()] is None:
                        self.jmp_path[-1][self.last_jxx.getAddress()]= str(instruction) # 这里存入相应的内容
                        self.cmp_path[-1][self.last_instruct.getAddress()] = str(instruction) # 
                        self.generate_new_path(instruction)
            elif len(self.jmp_path) == 0:
                pass
        elif instruction.getAddress() in self.switch_nodes: # 
            '''
                处理多分支，遇到jmp rax
            '''
            # 有分支不一定有循环，这次要记录 分支和本次的目标地址
            self.jmp_path.append({self.switch_nodes[instruction.getAddress()]:None})
            self.cmp_path.append({self.switch_nodes[instruction.getAddress()]:None})
            self.last_jxx = instruction
            # 只是遇到分支了，还不知道本次怎么跳转
        else:
            '''
                hook一般的jxx状态
            '''
            self.last_jxx = instruction
        # 缓存上一条指令和上上条指令
        self.last_last_instruction = self.last_instruct
        self.last_instruct = instruction
        if new_gadget is not None and new_gadget is not False and type(new_gadget) is not list:
            new_gadget.jmp_path = self.deepcopy_path(self.real_main_jmp_path)
            new_gadget.path_to_gadget = self.deepcopy_path(self.real_main_cmp_path)
    
    def get_main_path(self):
        # 该函数的返回值用于将当前的路径返回
        return deepcopy(self.main_jmp_path), deepcopy(self.main_cmp_path)

    def deepcopy_path(self,pointed_list):
        new_list = []
        for node in pointed_list:
            new_list.append(node)
        return new_list

    def generate_new_path(self,next_choice):
        '''
            路径生成策略：
                -   记录Switch结构，获取下一跳
                的地址
        '''
        next_node_jmp = []
        next_node_cmp = []
        # 一次生成肯定只会多产生一个节点
        if type(list(self.cmp_path[-1].keys())[-1]) is angr.knowledge_plugins.cfg.cfg_node.CFGNode: # 如果最后一个元素是Switch_mode
            for next_block in list(self.cmp_path[-1].keys())[-1].successors:
                if next_block.addr - ANGR_BASE + self.code_base == next_choice.getAddress():
                    # 维护一个当前路径，用于后续的路径生成
                    self.main_jmp_path.append({str(self.last_instruct):next_block.addr - ANGR_BASE + self.code_base})
                    self.main_cmp_path.append({str(self.last_instruct):next_block.addr - ANGR_BASE + self.code_base})
                    self.real_main_jmp_path.append({self.last_instruct:next_block.addr - ANGR_BASE + self.code_base})
                    self.real_main_cmp_path.append({self.last_instruct:next_block.addr - ANGR_BASE + self.code_base})
                if self.last_instruct.isTainted():
                # 如果当前jmp rax指令是被污染的则添加新的节点
                    next_node_jmp.append({str(self.last_jxx):next_block.addr - ANGR_BASE + self.code_base})
                    next_node_cmp.append({str(self.last_last_instruction):next_block.addr - ANGR_BASE + self.code_base})
        else:
            self.main_jmp_path.append({str(self.last_jxx):next_choice})
            self.main_cmp_path.append({str(self.last_cmp):next_choice})
            self.real_main_jmp_path.append({self.last_jxx:next_choice})
            self.real_main_cmp_path.append({self.last_cmp:next_choice})
            if self.last_instruct.isTainted():
                next_node_cmp.append({str(self.last_cmp):not next_choice})
                next_node_jmp.append({str(self.last_jxx):not next_choice})
        
        if self.fake_jmp_path is not None and len(self.fake_jmp_path) != 0:
            if type(next_choice) is not bool:
                tmp_node = {str(self.last_jxx):next_choice.getAddress()}
            else:
                tmp_node = {str(self.last_jxx):next_choice}
            if tmp_node in self.fake_jmp_path:
            # 在所有的路径都先消去写死的路径前缀
                assert self.fake_jmp_path[0] == tmp_node
                del self.fake_jmp_path[0]
                return
            raise Exception("NOT TARGET PATH!!!!!!")
        
        if not self.last_instruct.isTainted():
            # 如果没有被污染就不需要做生成新的路径操作
            return
        elif len(self.new_cmp_path)  == 0:
            # 此时还并没有产生新路径
            self.new_cmp_path += [next_node_cmp]
            self.new_jmp_path += [next_node_jmp]
            self.current_new_cmp.append(deepcopy(self.new_cmp_path))
            self.current_new_jmp.append(deepcopy(self.new_jmp_path))
        else:
            # 已经不是第一个新的节点

            for cmp_node, jxx_node in zip(next_node_cmp,next_node_jmp):
                # 替换生成新的节点
                my_jmp_path_pattern = deepcopy(self.main_jmp_path)
                my_jmp_path_pattern[-1] = jxx_node
                my_cmp_path_pattern = deepcopy(self.main_cmp_path)
                my_cmp_path_pattern[-1] = cmp_node
                # 记录新节点
                self.new_cmp_path.append(my_cmp_path_pattern)
                self.new_jmp_path.append(my_jmp_path_pattern)
                self.current_new_cmp.append(deepcopy(my_cmp_path_pattern))
                self.current_new_jmp.append(deepcopy(my_jmp_path_pattern))

    def get_current_new(self):
        return self.current_new_cmp, self.current_new_jmp 

    # 返回结果
    def get_result(self):
        return deepcopy(self.new_cmp_path), deepcopy(self.new_jmp_path)
    
    # 清理当前程序中的暂存变量
    def clean(self):
        self.current_new_cmp = list()
        self.current_new_jmp = list()

class loop_controller():
    def __init__(self,
                 file_path:str, # 该类用于对某个文件进行建模，提取其中对应的cdg图
                 loop_gate=3, # 这里暂定循环三次
                 cfg_model = None,
                 loop_list =None,
                 angr_proj = None
                 ) -> None:
        self.file_path=file_path
        # 创建angr对象
        if angr_proj is None:
            if NOW_ARCH == ARCH.X86_64:
                self.angr_proj=angr.Project(self.file_path, arch='x86_64',auto_load_libs=False)
            else:
                self.angr_proj=angr.Project(self.file_path, arch='x86',auto_load_libs=False)
        else:
            self.angr_proj = angr_proj
        import dill
        import sys
        if cfg_model is None:
            # 创建cfg图
            if not os.path.exists((sys.argv[1]).split('/')[-1]+'.cfg_model') :
                self.cfg = self.angr_proj.analyses.CFGEmulated(keep_state=True, 
                                        state_add_options=angr.sim_options.refs, 
                                            context_sensitivity_level=2)
                with open(str(sys.argv[1]).split('/')[-1]+'.cfg_model', 'wb') as f:
                    dill.dump(self.cfg, f)
            else:
                with open(str(sys.argv[1]).split('/')[-1]+'.cfg_model', 'rb') as f:
                    self.cfg = dill.load(f)
            # TODO增加存储self.cfg部分的代码
            
            if not os.path.exists((sys.argv[1]).split('/')[-1]+'.pathcfg'):
                # 保存分析结果，避免多次调试分析
                self.path_cfg = self.angr_proj.analyses.CFGFast()
                with open(str(sys.argv[1]).split('/')[-1]+'.pathcfg', 'wb') as f:
                    dill.dump(self.path_cfg, f)
            else:
                with open(str(sys.argv[1]).split('/')[-1]+'.pathcfg', 'rb') as f:
                    self.path_cfg = dill.load(f) 
        else:
            self.cfg = cfg_model
            self.path_cfg = cfg_model
        self.nx_cfg = self.cfg.graph
        self.cfg_edges=self.nx_cfg.edges
        # self.cfg_nodes=self.nx_cdg.nodes
        
        # print(self.cfg_fast)
        # 下面是用于循环管理的变量
        self.loop_gate = loop_gate # 鉴定循环次数   

        # 这里如果已经分析过就不用继续
        if loop_list is None:
            # 这里编写进行循环查找部分的代码
            if not os.path.exists((sys.argv[1]).split('/')[-1]+'.looplist') :
                self.angr_proj.analyses.CFGFast(symbols=False, start_at_entry=False,force_complete_scan=False, function_prologues=False, 
                                            # function_starts=[inst.getAddress()] # 这里需要先给出这个地址在哪个函数的
                                                )
                self.loop_list=self.angr_proj.analyses.LoopFinder().loops
                with open(str(sys.argv[1]).split('/')[-1]+'.looplist', 'wb') as f:
                    dill.dump(self.loop_list, f)
            else:
                with open(str(sys.argv[1]).split('/')[-1]+'.looplist', 'rb') as f:
                    self.loop_list = dill.load(f)
        else:
            self.loop_list = loop_list
        

        self.in_loop=False # 这里用于记录是否在一个循环中
        self.current_time=[]
        self.loop_stack=[] # 该结构用于记录当前所处的循环之中
        self.taint_flag=[]
        self.dispatcher=[]

        # 这里先将当前循环中的内容取出来构造映射表
        self.judge_node = {}
        self.out_edge = {}
        self.loop_dict = [] # 该字典用于记录当前函数中所有loop所包含的入度和出度
        self.loop_dict_bk = []
        self.next_wait = []
        for loop in self.loop_list:
            # 这里忽略了一些循环
            if len(loop.break_edges) != 0:
                    # 这里将当前的地址和循环映射关系记录
                self.loop_dict.append(loop.break_edges[0][0].addr)
                self.loop_dict_bk.append(loop.break_edges[0][-1].addr)
                self.out_edge[loop.break_edges[0][-1].addr] = loop
            # 这里将当前的地址和循环映射关系记录
            if len(loop.entry_edges) == 0:
                continue
            # 进入边的地址
            self.judge_node[loop.entry_edges[0][-1].addr] = loop
        
        '''
            以下内容是新添加的控制结构
        '''
        self.last_node = None
        self.last_call_or_loop = [] # 该参数用于检查上一次是call还是loop
             
    # 该函数的作用是清理上次运行产生的影响，便于下次继续
    def clear(self):
        self.in_loop=False # 这里用于记录是否在一个循环中
        self.current_time=[]
        self.loop_stack=[] # 该结构用于记录当前所处的循环之中
        self.taint_flag=[]
        self.dispatcher=[]
        self.last_node = None
        self.next_wait = [] # 这里是个栈结构，防止在等jxx跳出时遇到call指令进入到另一个过程中。其中只存储1和0两种数据，1：wait_jxx, 0: wait_ret,

    # 该函数的作用是设定loop_gate
    def set_loop_gate(self,loop_gate):
        self.loop_gate = loop_gate
    '''
        该函数的作用是给定一个地址，检测其是否在某个循环内
    '''
    def init_loop_controller(self):
        self.lp_stack = [] # 用于存储当前经过的循环
        self.lp_times = [] # 记录每个循环的循环次数
        self.force_break = []
        # print("[*] Loop Controller Init Finished")

    # 强制退出一个循环时
    def pop_loop(self):
        self.lp_stack.pop()
        self.lp_times.pop()
        self.force_break.pop()

    def control_loop_times(self, inst, ctx, base_addr,pc):
        ret_pc = None
        if len(self.force_break) != 0:
            if self.force_break[-1] is True:
                # 只有在存在强制退出要求时才会出现该结构的利用
                if inst.isBranch() and self.next_wait[-1] == 1:
                    '''
                        等待jxx并进行处理
                    '''
                    for per_bk_edge in self.lp_stack[-1].break_edges:
                        if pc - base_addr + ANGR_BASE == per_bk_edge[-1].addr:
                            # 这里自然退出了就不用管了
                            ret_pc = True
                            break
                    if ret_pc is None:
                        # 就是自己不跳转，那就强制跳转退出
                        if hex(pc) == get_jump_target(ctx=ctx,instruction=inst):
                            # 如果跳转成功，那就不让他成功
                            ret_pc = inst.getAddress() + inst.getSize()
                        else:
                            try:
                                ret_pc = int(get_jump_target(ctx=ctx,instruction=inst),16)
                            except:
                                # 这里证明是jmp rax
                                pass
                    # 这里直接清空一个循环
                    self.pop_loop()
                    self.next_wait.pop()
                    return ret_pc
                elif 'ret' in str(inst) and self.next_wait[-1] == 0:
                    '''
                        这里处理的是call的返回
                    '''
                    # 这里弹出选项
                    self.next_wait.pop()

                # 如果在等待强制退出的时候遇到call指令，需要向其中加入一个0，表示等待ret指令
                if 'call' in str(inst):
                    self.next_wait.append(0) # 检查当前程序中的wait

        # 检查当前指令位置
        if inst.getAddress()- base_addr + ANGR_BASE  in self.judge_node:
            # 此刻进入一个循环的起始位置
            if len(self.lp_stack) == 0:
                # 首次进入一个循环
                self.lp_stack.append(self.judge_node[inst.getAddress()- base_addr + ANGR_BASE ])
                self.lp_times.append(1)
                self.force_break.append(False)
                print("[*] First Enter a loop")
            elif self.lp_stack[-1].entry_edges[0][-1].addr == inst.getAddress()- base_addr + ANGR_BASE :
                # 第二次进入同一个循环
                self.lp_times[-1] += 1
                if self.lp_times[-1] > self.loop_gate:
                    # 循环次数太多,这里表示要进行强制退出
                    self.force_break[-1] = True
                    self.next_wait.append(1) # 这里表示在等待jxx指令进行强制跳出
            else:
                # 开始进行循环嵌套
                self.lp_stack.append(self.judge_node[inst.getAddress()- base_addr + ANGR_BASE ])
                self.lp_times.append(1)
                self.force_break.append(False)
            return None
        # 检查当前循环是否存在退出
        elif len(self.lp_stack) != 0:
            for per_bk_edge in self.lp_stack[-1].break_edges:
                if inst.getAddress() - base_addr + ANGR_BASE  ==  per_bk_edge[-1].addr:
                    self.pop_loop()
                    return None

        return None
            

    def find_loop_by_inst(self,inst,check_func,base_addr):
        ret_loop_stack = []
        lop_flag = -2
        whether_taint=False
        if 'call' in str(inst):
            self.last_call_or_loop.append(inst) # 这里记录一个call
        
        if type(inst) is int:
            inst_addr = inst - base_addr+ANGR_BASE if base_addr is not None else inst
        else:
            # 这里判断下一个指令的地址目的是用于循环跳出
            inst_addr = inst.getNextAddress() - base_addr + ANGR_BASE if base_addr is not None else inst.getNextAddress()
        # 如果都不在就直接返回
        if inst_addr not in self.judge_node and inst_addr not in self.loop_dict_bk and len(self.loop_stack) == 0:
            return [ret_loop_stack,whether_taint], -2
        '''
            一个结点可能同时是一个循环的break和另一个循环的entry
        '''
        if len(self.loop_stack) != 0:
            if self.check_in_break(self.loop_stack[-1],inst_addr):
                # 如果是在当前的break_node中，则进行break操作
                if DEBUG:
                        print(">>>>>>> 退出循环",hex(inst_addr))
                self.loop_stack.pop()
                self.taint_flag.pop()
                self.current_time.pop()
                if len(self.loop_stack) == 0:
                    self.in_loop = False 
                ret_loop_stack=deepcopy(self.loop_stack)
                whether_taint = deepcopy(self.taint_flag)
                lop_flag = 1
                # 不会存在没有ret但循环退出的情况
                self.last_call_or_loop.pop() # 这里将栈进行pop
        if (inst_addr in self.judge_node.keys() and self.in_loop is False) or \
            (inst_addr in self.judge_node.keys() and self.judge_node[inst_addr].entry_edges[0][-1].addr != self.loop_stack[-1].entry_edges[0][-1].addr): # 退出子循环进入下一个子循环
            if check_func is not None:
                whether_taint = check_func(inst,None) # 使用该函数检查当前指令的污染情况
            self.loop_stack.append(self.judge_node[inst_addr])  # 这里不用担心多次记录loop，后面有in_loop标志位标记是否已经在走过
            self.taint_flag.append(whether_taint)
            self.last_call_or_loop.append(self.judge_node[inst_addr])
            # 此处刚好进入一个循环,一切重新开始计算
            self.in_loop = True 
            self.current_time.append(0)
            ret_loop_stack=deepcopy(self.loop_stack)
            whether_taint = deepcopy(self.taint_flag)
            self.last_call_or_loop.append(self.judge_node[inst_addr]) # 这里记录一个loop
            return [ret_loop_stack,whether_taint], 0
        
        # 这里不应该根据边进行判断，这里应该根据结点进行判断
        elif len(self.loop_stack) != 0:
            if self.loop_stack[-1].entry_edges[0][-1].addr == inst_addr: # 再次进入判断节点，此处是进行新的一轮循环 == loop.break_edges[0][0].addr and self.in_loop is True and loop in self.loop_list 
                # 进入新的一轮循环,进行单纯地记录循环次数即可
                self.current_time[-1] += 1
                lop_flag = 2 # 同一个跳转进入了第二次
                ret_loop_stack=deepcopy(self.loop_stack)
                whether_taint = deepcopy(self.taint_flag)
                if self.current_time[-1] > self.loop_gate: # 当前的循环可以跳出
                    ret_loop_stack=deepcopy(self.loop_stack) # 记录的是实际应该返回的地址 
                    whether_taint = deepcopy(self.taint_flag)
                    
                    lop_flag = -1 # 本次进入后应该退出
                    self.last_call_or_loop.pop() # 取出最后一个一定是loop
                    self.loop_stack.pop()
                    self.taint_flag.pop()
                    self.current_time.pop()
                    if len(self.loop_stack) == 0: # 如果当前不在任何循环中就将其设置为False
                        self.in_loop = False # 这里进行循环的强制跳出
                    return [ret_loop_stack,whether_taint] , lop_flag # 其实这里可以结束并返回了，第一个返回值是实际要走向的地址，第二个位置是标志位，标明当前需要进行的各种操作
                return [ret_loop_stack,whether_taint] , lop_flag
            elif  'ret' in str(inst) and self.in_loop is True:
                # 上一次是call，则不用操作
                if type(self.last_call_or_loop[-1]) == type(inst):
                    self.last_call_or_loop.pop()
                else:
                    # 上次的操作是loop，则退出当前的所有loop
                    while type(self.last_call_or_loop.pop()) == type(inst):
                        # 这里退出相同的次数
                        self.loop_stack.pop()
                        self.taint_flag.pop()
                        self.current_time.pop()
                    if len(self.loop_stack) == 0:
                        self.in_loop = False 
                    ret_loop_stack=deepcopy(self.loop_stack)
                    whether_taint = deepcopy(self.taint_flag)
                    return [ret_loop_stack,whether_taint], 1 # 标明无任何问题，正常退出即可

            # 只有退出当前的循环才算真正的退出，这里ret退出的前提call发生在进入loop之前
            elif (self.check_in_break(self.loop_stack[-1],inst_addr)) and self.in_loop is True: # 如果当前正好自然执行到break的位置
                '''
                    这里增加一个修正的部分，如果当前退出循环时，该循环体内的
                '''
                if DEBUG:
                    print(">>>>>>> 退出循环",hex(inst_addr))
                self.loop_stack.pop()
                self.taint_flag.pop()
                self.current_time.pop()
                self.last_call_or_loop.pop()
                if len(self.loop_stack) == 0:
                    self.in_loop = False 
                ret_loop_stack=deepcopy(self.loop_stack)
                whether_taint = deepcopy(self.taint_flag)
                return [ret_loop_stack,whether_taint], 1 # 标明无任何问题，正常退出即可
            elif self.in_loop == True: # 如果当前在循环之中
                ret_loop_stack = deepcopy(self.loop_stack)
                whether_taint = deepcopy(self.taint_flag)
        return [ret_loop_stack,whether_taint], lop_flag
    

    def check_in_break(self, loop, addr):

        if len(loop.break_edges) == 0:
            return True
        
        if loop.break_edges[0][-1] == addr:
            return True
        return False

    def search_cycle(self,
                     inst, # 目标跳转指令所在位置
                     check_func,
                     base_addr
                     ):
        return self.find_loop_by_inst(inst,check_func,base_addr)
        