from dataflow_analysis.data_flow_analyse import *
from utils.log_func import *
from copy import deepcopy
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,AST_REPRESENTATION,CALLBACK
from utils.libc_func_mod32 import *
from utils.tool_lib import *
from path_controller.cycle_class import *
from config.__config import *
ANGR_BASE = 0x400000
def get_memory_overlaps(Cache, start, end, tainted_mem, flag):
        overlaps = []
        for block in Cache:
            # Check if the block overlaps with the given range
            if block['start'] < end and block['start'] + block['size'] > start:
                # Calculate the overlap between the block and the given range
                overlap_start = max(block['start'], start)
                overlap_end = min(block['start'] + block['size'], end)
                overlap_size = overlap_end - overlap_start
                permissons = block['permissions']
                name = block['name']
                if name == 'mapped' and block['start'] <= list(tainted_mem.keys())[0] and (block['size']+block['start']) >= list(tainted_mem.keys())[0] : 
                    # Add the overlap to the list
                    if flag in permissons:
                        overlaps.append({
                            'start': overlap_start,
                            'size': overlap_size,
                            'permissions': permissons,
                        })
        return overlaps
gadget_match_mod={} # 该结构用于记录各各个gadget之间的匹配关系
# 该结构用于记录当前已经发现的gadget对
# 数据流控制结构
class Data_flow_controler():
    def __init__(self,
                 ctx,
                 start_address, # 用于记录数据流分析的起始位置
                 code_cache,
                 finish_address = None,
                 mem_cache = None,
                 tainted_mem = None,
                 ) -> None:
        self.start_address = start_address # 记录起始位置
        self.Dataflow=DataflowAnalysis(ctx= ctx , pc = start_address,memoryCache = mem_cache,codeCache=code_cache) # 创建数据流对象
        self.start_flag = False
        self.finish_address = finish_address
        self.result = dict() # 使用一个字典存储当前的分析结果
        self.mem_cache = mem_cache
        self.tainted_mem  = tainted_mem
        self.gdt_pair = []
        self.analyse_mod = 'data_range' 
        # 

    def fresh(self):
        self.Dataflow=DataflowAnalysis() 
        self.start_flag = False

    def get_result(self):
        return self.result

    def set_analyse_mod(self,mod):
        self.analyse_mod = mod
    def build_taint_ability(self,inst,ctx,gadget=None,check=False):
        target_=inst.getOperands()[0] # 获取目标寄存器
        if target_.getType()==OPERAND.MEM and (check == True or self.Dataflow.check_data_dependency(self.start_address,inst.getAddress())): # 这里
            base_reg=target_.getBaseRegister() # 获取基址寄存器
            if ctx.isRegisterTainted(base_reg): # 检查当前写入的目标地址是否是可控的，如果是可控的就构建其表达式
                base_reg_name = str(base_reg).split(':')[0] # 获取目标地址
                pointer_range = self.Dataflow.get_reg_range_in_dfgs(self.start_address,inst.getAddress(),1, base_reg_name)
                new_range = get_memory_overlaps(self.mem_cache,pointer_range[0],pointer_range[-1],self.tainted_mem,'w')
                self.result['target_range'] = new_range
                return True
            else: 
                pass
        elif target_.getType()!=OPERAND.MEM:  
            pass
        else:
            pass

    def build_data_flow_by_inst(self, inst, ctx, reg_name:str,position_name:str):
        reg_range = self.Dataflow.get_reg_range_in_dfgs(self.start_address,inst.getAddress(),1, reg_name, ctx)
        self.result[position_name] = reg_range

    def build_libc_gadget(self,ctx,inst,libc_gdt_mod): # 这里需要传入的部分是
        '''
            该函数的作用是对当前的库函数gadget进行建模
        '''
        # 获取目标地址的取值范围
        for per_inst in libc_gdt_mod.instructions:
            if 'di' in str(per_inst.instruction): # 如果寄存器在当前的指令中
                addr = per_inst.instruction.getAddress()
                pointer_range = self.Dataflow.get_reg_range_in_dfgs(self.start_address,per_inst.instruction.getAddress(),1, 'rdi')
                new_range = get_memory_overlaps(self.mem_cache,pointer_range[0],pointer_range[-1],self.tainted_mem,'w')
                libc_gdt_mod.taint_range = {'target_range':new_range}
                return
        raise Exception("NOT FOUND RDI")

    # 该函数的作用是检查两个残缺gadget能否进行缝合操作
    def check_incomplete_gdt(self, inst, ctx, gdt_list, gadget):
        if gadget.gadget_type in ['AMCgadget','AMWgadget','AMRgadget','state target read gadget']:
            reg2 = 'rsi'
            for inst in gadget.instructions:
                    if 'si' in str(inst.instruction):
                        addr2 = inst.instruction.getAddress()
                        #  这里找到相应的地址
                        break
        elif gadget.gadget_type ==  'assignment':
            target_ = gadget.instructions[0].instruction.getOperands()[0] # assignment的最后一条指令一定会进行内存值写回操作
            if target_.getType()!=OPERAND.MEM:
                return
            base_reg=target_.getBaseRegister()
            reg2 = str(base_reg).split(':')[0] 
            addr2 = gadget.instructions[0].instruction.getAddress()
        else:
            return

        for pri_gdt in gdt_list:
            reg1 = None
            addr1 = None
            if pri_gdt.gadget_type in ['AMCgadget','AMWgadget']: 
            
                reg1 = 'rdi'
                for inst in pri_gdt.instructions:
                    if 'rdi' in str(inst.instruction):
                        addr1 = inst.instruction.getAddress()
                        break
            elif pri_gdt.gadget_type ==  'assignment': 
                target_=pri_gdt.instructions[-1].instruction.getOperands()[0] # assignment的最后一条指令一定会进行内存值写回操作
                assert target_.getType()==OPERAND.MEM
                base_reg=target_.getBaseRegister()
                reg1 = str(base_reg).split(':')[0] 
                addr1 = pri_gdt.instructions[-1].instruction.getAddress()
            else:

                continue
            if reg1 is None or addr1 == addr2:
                continue

            if self.Dataflow.check_data_dependency(self.start_address,addr1,reg1,addr2,reg2,ctx):

                self.gdt_pair.append([pri_gdt,gadget])

    def solve(self, inst, ctx, hooking_flag, gadget = None,gdt_list = []):
        self.Dataflow.collect_opcode(inst,hooking_flag) # 收集当前的指令
        if inst.getAddress() == self.start_address:
            self.start_flag = True
        elif self.start_flag == False:
            # 该位置不做任何处理
            return None

        final = False
        if gadget is not False and gadget is not None and self.finish_address is None: # 这里从外部传入，当前是否到达了某个gdt，并且不是在搜索模式
            if self.analyse_mod == 'data_dep':

                self.check_incomplete_gdt(inst, ctx, gdt_list,gadget)

            
            elif 'jmp' in str(inst) or 'call' in str(inst):
                # 对当前的库函数gdt进行分析

                if 'AMW' in gadget.gadget_type or 'AMC' in gadget.gadget_type:
                    self.build_libc_gadget(ctx,inst,gadget)  # 这里传入的是指令序列
                    final = False
            else:
                final = None
                final = self.build_taint_ability(inst,ctx,gadget,check=True)

                
        if self.finish_address is not None and self.finish_address == inst.getAddress():
            final = self.build_taint_ability(inst,ctx,gadget)

        if final:
            return self.get_result() # 这里直接返回对应的污染范围
        else:
            return None
            

        


class path_with_gdt_pair():
    def __init__(self,
                j_path,
                c_path,
                gdt_pair_list=[],# 该结构用于记录当前路径下有多少gadget对，存储方式[[g1,g2],[g3,g4]]
                ) -> None:
        self.j_path = j_path
        self.c_path = c_path
        self.gdt_pair_list = gdt_pair_list 


class gagdet_manager():
    def __init__(self,
                 gadget_list,
                 analyser_manager, # 这里需要上下文执行器进行继续执行
                 G_cmp_path_list, # 当前结构用于记录所有存在gadget的路径
                 G_jmp_path_list # 
                 ) -> None:
        self.gadget_list = gadget_list
        self.analyser_manager = analyser_manager
        self.G_jmp_path_list = G_jmp_path_list
        self.G_cmp_path_list = G_cmp_path_list
        self.code_base_adr = None
        self.real_dispatcher = {}
        
        self.gadget_pair_list = [] # 该结构中的每一个元素都是一个路径对象， 该路径对象中记录在其上的gdt对

    def check_same_path(self,gdt_pair:tuple):

        g1_path = gdt_pair[0].path_to_gadget
        g2_path = gdt_pair[-1].path_to_gadget
        # 如果当前的两个gdt路径并不相同
        if len(g1_path) != len(g2_path):
            return False
        else:
            for p1,p2 in zip(g1_path,g2_path):
                if p1!=p2 or g1_path[p1] != g2_path[p2]:
                    return False
            return True
        
    # 返回True和False，用于检查loop是不是同一个
    def check_whether_loop_in_list(self,peer_loop, tmp_dis_list):
        for tmp_loop in tmp_dis_list.keys():
            if (tmp_dis_list[tmp_loop][0].entry.addr == peer_loop.entry.addr):
                return True
        return False
    
    def build_dispatcher_gdt_ability(self,code_base_adr):

        self.code_base_adr = code_base_adr 
        loop_addr_to_gdt = {} 
        loop_addr_to_path_list = {} 
        for gdt in self.gadget_list: 
            if len(gdt.gadget_loop.loop_mod) == 0:
                continue
            for per_loop in gdt.gadget_loop.loop_mod[0]:
                if per_loop.entry.addr not in loop_addr_to_gdt.keys():
                    loop_addr_to_gdt[per_loop.entry.addr] = [gdt] # 记录当前的gadget
                    loop_addr_to_path_list[per_loop.entry.addr] = [gdt.path_to_gadget] # 
                else:
                    loop_addr_to_gdt[per_loop.entry.addr].append(gdt)
                    loop_addr_to_path_list[per_loop.entry.addr].append(gdt.path_to_gadget) # 这里要记录每一个
            
            gdt.analyse_gadget(code_base_adr) # 这里先对赋值gadget做操作
            

        for per_lop in loop_addr_to_gdt:
            # 这里是取出当前dispatcher控制的所有gdt
            controled_gadget_list = loop_addr_to_gdt[per_lop] # 这里取出每个
            controled_gadget_list = find_duplicates(controled_gadget_list) # 取出其中独一无二的路径
            if len(controled_gadget_list) > 1: # 如果当前dispatcher下至少有两条可达路径，那么说明其至少是个分发器
                self.real_dispatcher[per_lop] = controled_gadget_list # 这里记录下被其所控制的gdt

    def get_common_path(self,path1,path2):
        common_path = {}
        p1 = list(path1.items())
        p2 = list(path2.items())
        n = min(len(p1), len(p2))
        i = 0
        while i < n and p1[i][0] == p2[i][0] and p1[i][1] == p2[i][1]:
            common_path[p1[i][0]] = p1[i][1]
            i += 1
        path1_remain = {}
        path2_remain = {}
        if i < len(p1):
            for j in range(i, len(p1)):
                path1_remain[p1[j][0]] = p1[j][1]
        if i < len(p2):
            for j in range(i, len(p2)):
                path2_remain[p2[j][0]] = p2[j][1]
        return common_path,  path1_remain,  path2_remain


    def sew_all_gadget(self):


        # 首先遍历路径,这里是对单个路径做分析
        for j_path, c_path in zip(self.G_jmp_path_list,self.G_cmp_path_list):
            # 这里创建一个新的路径对象
            new_path_obj = path_with_gdt_pair(j_path=j_path,c_path=c_path)
            # 取出两个当前路径做模拟执行分析
            symbol_mem_map = self.analyser_manager.exe_symbolic(
                start_addr = None, # 这里使用默认起始位置即可
                current_path = j_path, # 这里记录的是jmp指令所在的位置
                path_for_emu = c_path,# 这里用于标注cmp指令
            )
            if symbol_mem_map is None:
                print("untouchable path!")
                return None, None
            
            for mem_addr in symbol_mem_map:
                self.analyser_manager.ctx.setConcreteMemoryAreaValue(mem_addr, bytes(chr(symbol_mem_map[mem_addr]).encode()))
                self.ctx.taintMemory(mem_addr, CPUSIZE.BYTE) # 设置对应的内存污染
                self.ctx.symbolizeMemory(MemoryAccess(mem_addr,CPUSIZE.BYTE))

            # 创建临时类
            class sew_solver():
                def __init__(self,gdt_list) -> None:
                    self.gdt_list = gdt_list 
                    self.gadget_map = {} # 当前的地址列表冗余 {inst1.addr:[inst1,inst2,inst3]}
                    for gdt in self.gdt_list:
                        self.gadget_map[gdt.instructions[0].instruction.getAddress()]=gdt.instructions # 这里面存储的是per_inst_in_stack 对象
                    # 下面的结构用于动态进行
                    self.approached_gadget = [] # 其中的每一个元素都是 gadget_mode
                    self.data_source_addr = [] # 记录当前所有可能的起点
                    self.approached_queue = [] # 当前的结构用于记录已经发现的gadged串
                    self.sewn_gadget=[]  # 该结构用于记录当前的gadget对，分别用于存储g1和g2 [[g1,g2]]
                    self.Dataflow = DataflowAnalysis()
                
                # 该函数用于进行gadget的整理
                def arrange_all_gadget(self):
                    # 当前函数将所有能够串联在一起的gadget进行整理
                    return self.sewn_gadget

                def solve(self,inst,ctx): # 该函数需要接收一个指令输入，并记录当前的状态
                    # 调用接口构建数据流
                    self.Dataflow.collect_opcode(inst) # 这里无脑读入指令构建数据流
                    if inst.getAddress() in self.gadget_map: # 如果当前的指令恰好在指令映射表里，则表明到达了一个gadget
                        # 如果找到的第一个gadget不是赋值gadget那么其本身是没什么意义的，非赋值gadget让他在数据流里存在即可
                        if len(self.approached_gadget) == 0 and self.gadget_map[inst.getAddress()].gadget_type == 'assignment':
                            self.approached_gadget.append(self.gadget_map[inst.getAddress()]) # 这里取出其中的gadget对象
                            self.data_source_addr.append(self.gadget_map[inst.getAddress()].instructions[-1].instruction.getAdress()) # 这里取出对应的指令地址
                        else:
                            # 如果找到了当前路径的第二个gadget,则构建二者之间的数据流关系,这里不区分是不是赋值gadget，运算gadget也有意义
                            # 构造所有已有gadget与当前gadget之间的关系
                            # 取出当前gdt所到达的指令地址
                            current_addr = self.gadget_map[inst.getAddress()].instructions[-1].instruction.getAdress()
                            prior_addr = [] # 记录先前已经发现的gdt地址有哪些
                            for prior_gadget in self.approached_gadget:
                                # 这里使用所有已经发现的gdt和当前的gdt做一个数据流上的检查 
                                prior_addr.append(prior_gadget.instructions[-1].instruction.getAdress()) # 收集先前找到的gdt地址
                            # 这里构造出所有需要的数据流图
                            self.Dataflow.data_flow_analyse(prior_addr,[current_addr]*len(self.data_source_addr),1) # 构造出相应的表达式
                            for prior_gadget in self.approached_gadget:
                                if self.Dataflow.check_data_dependency(prior_gadget.instructions[-1].instruction.getAdress(),current_addr): # 检查当前的依赖性
                                    # 如果二者存在关系，则取出索引寄存器， mov [rdi+index+0x8], rax  这里获取对应的寄存器，取出相应的rdi进行检查
                                    target_=self.gadget_map[inst.getAddress()].instructions[-1].instruction.getOperands()[0]
                                    if target_.getType()==OPERAND.MEM:
                                        # 这里需要进行检查，如果基地址寄存器本身
                                        base_reg=target_.getBaseRegister() # 获取基址寄存器
                                        if ctx.isRegisterTainted(base_reg): # 检查当前写入的目标地址是否是可控的，如果是可控的就构建其表达式
                                            base_reg_name = str(base_reg).split(':')[0] # 获取目标地址
                                            # 源地址 ， 目的地址， 寄存器名称：str
                                            expression_base_reg = self.Dataflow.regs_z3_exprs[prior_gadget.instructions[-1].instruction.getAdress()][current_addr][base_reg_name]
                                            self.Dataflow.find_range(base_reg_name) # 构建对应的
                                        else: 
                                            pass
                                    else:
                                        pass

                                    self.sewn_gadget.append([prior_gadget,self.gadget_map[inst.getAddress()],expression_base_reg]) # 这里找到对应的gadget对之间的关系
                            self.approached_gadget.append(self.gadget_map[inst.getAddress()]) # 将已捕获的gadget加入之前的内容中
                            self.data_source_addr.append(current_addr) # 

            my_sew_solver = sew_solver()
            emulator = vm_emulator(
                taint_analyser= self.taint_analyser,# 这里传入一
                code_base_adr = self.code_base_adr # 这里传入的程序的基地址
            )
            emulator.emu_ign(
                start_addr=self.analyser_manager.initial_entry_point, # 起点就是当前分析器的起始位置
                end_addr= None, # 这里让其自然运行到退出即可
                record_model_list=[my_sew_solver], # 此处记录用于进行gadget串联的对象
            )
            
            new_path_obj.gdt_pair_list.append(my_sew_solver.arrange_all_gadget()) # 这里是获取当前路径中的所有gadget串，注意这里是针对一条路径的
            # 这里不是简单的重新加入，需要将之前具有相同路径的对象做移除操作
            for per_pari_obj in self.gadget_pair_list:
                if per_pari_obj.j_path == new_path_obj.j_path:
                    self.gadget_pair_list.remove(per_pari_obj) # 这里将先前的对象移除
            self.gadget_pair_list.append(new_path_obj) # 记录当前找到的所有gadget串,该对象记录的是当前路径和gdt对之间的关系



    def ign_all_gadget(self,code_base_adr,bin_path): # 当前函数的作用是进行gadget之间的激活
        gadget_tmp = self.gadget_list
        # 这里是对当前列表里的每一个gadget做分析
        for gdt in gadget_tmp:
            ret_addr = gdt.instructions[-1].instruction.getAddress() #  获取状态的地址为gadget的首条指令
            '''              该函数执行结束后返回一个ctx上下文状态
            '''
            RESULT_log("analysing G1:",True)
            for inst in gdt.instructions:
                print(inst.instruction)
            myPath_solver = path_solver(bin_path,code_base_adr)
            ret_ctx,next_addr = self.analyser_manager.emu_single_path(
                record_model_list = [myPath_solver],
                current_jmp_path = gdt.jmp_path, # 这里记录的是jmp指令所在的位置
                current_cmp_path = gdt.path_to_gadget,# 这里用于标注cmp指令
                mem_map = False,  # 这里设置一个非None值
                tainted_address = [],
                gadget_address = [],
                get_state_addr = ret_addr,
                target_addr = ret_addr
            )
            state_gdt_jmp_path , state_gdt_cmp_path = myPath_solver.get_main_path()
            # 固定gadget路径
            myPath_solver.set_state_path(state_gdt_jmp_path,state_gdt_cmp_path)
            last_instruct = gdt.instructions[-1].instruction # 获取最后一条指令，对于内存操作的最后一条一般都是进行写回操作如果是memcpy则另做处理
            taint_size = last_instruct.getStoreAccess()[0][0].getBitSize() # 获取单次连续污染的最大长度
            if len(gdt.instructions[-1].taint_rec_dict['ta']) != 0: # 如果不是固定地址污染
                min_addr = gdt.taint_range['target_range'][0]
                max_addr = gdt.taint_range['target_range'][-1]
            base_addr = min_addr['start']
            max_addr = base_addr + min_addr['size']
            while base_addr < max_addr:
                ret_ctx.taintMemory(MemoryAccess(base_addr,CPUSIZE.DQQWORD))
                ret_ctx.symbolizeMemory(MemoryAccess(base_addr,CPUSIZE.BYTE))
                base_addr += CPUSIZE.DQQWORD
            base_addr = min_addr['start']
            self.analyser_manager.clear_gadget_rec() # 对当前gadget的记录做一个清理

            self.analyser_manager.dataflow_controller.set_analyse_mod('data_dep') # 设置当前的分析模式为检查关联性
            # 再次进行路径探索查找gadget,对所有的路径进行查找
            self.analyser_manager.search_path(
            tainted_address=[],
            start_address = next_addr,
            gadget_address=[],
            record_model_list=[myPath_solver,
                               # self.analyser_manager.dataflow_controller
                               ],
            pathSolver = myPath_solver,
            tainted_mem = [base_addr, max_addr],
            G1 = gdt
            )
            break
def find_duplicates(lst):
    duplicates = []
    for i in lst:
        if i not in duplicates:
            duplicates.append(i)
    return duplicates


class dispatcher():
    def __init__(self,
                loop_mod:list, 
                ) -> None:
        self.loop_mod = loop_mod
    

# 该类用于对gadget进行建模
class gadget_mode():
    def __init__(self,
                 gadget_type:str, # 此处用于定义gadget的类型,使用字符串标注
                 instructions:list, # 此处用于定义指令序列，其中每一个元素都是指令对象per_inst_in_stack
                 path_to_gadget:dict, # 此处记录到达gadget的路径 {cmp指令地址：True/False}
                 gadget_loop, #该位置用于存放gadget所处于的那个
                 g_jmp_path, # 记录gadget的jmp路径
                 taint_analyser, # 这里传入的是一个污点分析器
                 ) -> None:
        self.gadget_type=gadget_type 
        self.instructions=instructions
        self.path_to_gadget=path_to_gadget 
        self.gadget_loop=dispatcher(loop_mod=gadget_loop) # 这里的gadgetloop分类两部分，第一部分是一组循环的集合，第二部分是相应的循环的污染情况
        self.gdt_code = None # 该变量用于标识出当前的gadget属于哪一种类型
        self.taint_analyser = taint_analyser # 这里是将对应的污点分析器进行
        self.enhancer = None # 该结构用于记录当前gadget中存在的增强器结构
        self.enhancer_variable = None # 该变量记录当前增强器的受控内容
        self.jmp_path = g_jmp_path # 记录当前的跳转节点
        self.taint_range = None
        self.gdt_attribute = None # 记录当前gdt的属性

    # 该函数用于添加污染范围
    def add_taint_range(self,new_range):
        self.taint_range = new_range 

    # 该函数注重对于当前gadget及其dispatcher之间的关系进行分析
    def analyse_gadget(self,code_base_adr):
        if self.gadget_type == 'assignment':

            # 这里检查每一条指令的污染情况
            start_inst = self.instructions[0] # 这里取出的是第一个inst obj
            end_inst = self.instructions[-1] # 这里取出的是最后一个inst obj
            # 检查AMC
            if start_inst.taint_rec_dict['sa'] is not None and end_inst.taint_rec_dict['ta'] is not None:
                # 首条指令的地址源地址，和最后一条指令的目标地址
                self.gdt_attribute = 'AMC'
            # 检查AMR
            elif start_inst.taint_rec_dict['sa'] is not None and end_inst.taint_rec_dict['ta'] is None:
                # 源地址任意，目标地址固定
                self.gdt_attribute = 'AMR'
            # 检查AMW
            elif start_inst.taint_rec_dict['sm'] is not None and end_inst.taint_rec_dict['ta'] is not None:
                # 将用户缓冲区中的内容写到任意位置，其实也就是地址可控的任意写
                self.gdt_attribute = 'AMW'

            index_reg = []
            # 这里对赋值gadget做分析处理
            for ins in self.instructions: # 既然是赋值gadget那么就要做检查每次赋值中的寄存器索引在当前循环中是不是存在自加等操作
                if 'ret' in str(ins.instruction):
                    continue
                target=ins.instruction.getOperands()[0] # 取出第一个参数，是一个写回操作
                if target.getType() == OPERAND.MEM:
                    if 'unknown' not in str(target.getIndexRegister()) and target.getIndexRegister() not in index_reg:
                        index_reg.append(target.getIndexRegister()) # 这里是记录对应的索引寄存器
                target=ins.instruction.getOperands()[-1] # 取出写回位置的索引
                if target.getType() == OPERAND.MEM:
                    if 'unknown' not in str(target.getIndexRegister()) and target.getIndexRegister() not in index_reg:
                        index_reg.append(target.getIndexRegister()) # 
            if len(index_reg) == 0:
                # 当前的gadget中不存在增强器结构
                return False
            '''
                index_reg到此处已经记录了在复制gadget中用于索引的寄存器
            '''
            near_loop = self.gadget_loop.loop_mod[0][-1] # 这里取出最近的一个循环
            near_loop_taint_rec = self.gadget_loop.loop_mod[-1][-1]
            # 这里取出其中的数据流
            '''
                数据流方案：检查从单次执行循环体开始到执行循环体结束这一段数据流的流动情况

                代码分析方案：使用模拟执行，检查其自然进入下一次循环时，是否对相应的寄存器做了加一操作
            '''
            
            emulator = vm_emulator(
                taint_analyser= self.taint_analyser,# 这里传入一
                code_base_adr = code_base_adr
            )
            # 开始进行模拟分析
            is_Enhancer = emulator.emu_ign(
                            start_addr = near_loop.break_edges[0][0].addr, # 此处对当前的
                            end_addr = near_loop.break_edges[0][-1].addr, # 跳出当前循环的，这里如果不只一个breakedges怎么办
                            watch_oprand=index_reg,# 此处用于记录当前的寄存器
                )
            if is_Enhancer:
                # 这里取出对应的loop的参数，合并构筑gadget能力
                self.enhancer = near_loop # 该结构用于记录增强器
                self.enhancer_taint_dict = near_loop_taint_rec # 该结构用于记录增强器的受污染状态
                '''
                    此处是否应该检查增强器的能力
                '''
                if len(near_loop_taint_rec['sm']) != 0:
                    target_mem_addr = near_loop_taint_rec['sm'][0][0]
                    target_mem_length = near_loop_taint_rec['sm'][0][-1] # 获取控制变量的长度
                    self.enhancer_variable  = MemoryAccess(target_mem_addr,target_mem_length) # 这里开始构建内存访问对象
                    self.enhancer_variable  =  target_mem_length
                
        elif self.gadget_type == 'operating': # 如果当前的gadget是运算gadget
            pass






