from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,AST_REPRESENTATION,CALLBACK
import sys
import os
import random
import pickle
from threading import Thread,Lock
from utils.evalib import *
from time import time
'''
    自定义函数库调用
'''
from gadget_manager.gadget_mod import *
from utils.log_func import * 
from utils.ctx_initer import *
from utils.tool_lib import *
from utils.libc_func_mod64 import customRelocation64
from path_controller.sym_emulator import per_path_contatiner,path_emulator,slight_touch,slight_slight_touch# 这里引用出路径记录
from path_controller.cycle_class import *
from config.__config import *
from config.__thread_global import *
from fuzzywuzzy import fuzz
from path_controller.smart_sort import *
'''
    全局参数
'''

#  该变量用于存储当前程序中的gadget和相应重定位地址之间的映射，加速查找速度
GadgetFunc2Addr = {}
BASE_ADDR = None 
binary = None # 这里是全局的二级制文件
dump_data = None # 该变量用于存储dump文件
MEM_MAP = None # 该变量存放的是当前的内存布局
customRelocation = None
BRANCH_MAP = None # 存储静态分析结果
ANGR_PROJ = None
CFG_MODEL = None
LOOP_LIST = None

# 获取线程锁定
counter_lock = Lock()
memoryCache = list()
codeCache = list()
START_TIME = time()


def load_dump(ctx, dump_local_path,binary_name):
    global memoryCache
    global codeCache 
    global dump_data
    # Open the dump
    if dump_data is None: # 这里如果还没有读出来过数据
        with open(dump_local_path,'rb') as file:
            dump_data = pickle.load(file,encoding='iso-8859-1')

    regs = dump_data[0]
    mems = dump_data[1]
    codes = dump_data[2]
    args = dump_data[3]
    # Load registers into the ctx
    # print('[+] Define registers')
    for reg_name in regs:
        try:
            Reg = ctx.getRegister(reg_name)
        except:
            print("[-] WARNING: illegal Register:",reg_name)
            continue
        ctx.setConcreteRegisterValue(Reg, regs[reg_name])
    if 'rip' in regs:
        entrypoint = regs['rip']
    else:
        entrypoint = regs['eip']
    real_base_flag = False
    got_base_got_adr = False
    #print('[+] Define memory areas')
    for mem in mems:
        start = mem['start']
        end   = mem['end']
        name = mem['name']
        permissions = mem['permissions']
        if mem['memory']:
            memoryCache.append({
                'start':  start,
                'size':   end - start,
                'memory': mem['memory'],
                'permissions':mem['permissions'],
                'name': mem['name']
            })
        argv1=str(sys.argv[1]).split('/')[-1] # 取出so文件名称
        # got表在so文件对应的可读可写段
        if argv1 in name and 'rw' in permissions and not got_base_got_adr:
            base_got_adr=start
            got_base_got_adr = True
        
        if binary_name in mem['name'] and 'r--p' in permissions and not real_base_flag:
            real_base = mem['start']
            real_base_flag = True
    got_code_base_adr = False
    for code in codes:
        start = code['start']
        end   = code['end']
        #print('[+] code caching %x-%x' %(start, end))
        if code['memory']:
            codeCache.append({
                'start':  start,
                'size':   end - start,
                'memory': code['memory'],
                'permissions':code['permissions'],
                'name': code['name']
            })
        if binary_name in code['name'] and not got_code_base_adr:
            code_base_adr = code['start']
            got_code_base_adr = True
    
    # 下面这一部分load plt表，暂时来看不需要了

    return entrypoint, base_got_adr, args, code_base_adr, real_base

# 漏洞触发点代码所在段的基址
base_adr = 0

# caching on the fly to speed up the dump loading.
def Caching(ctx, mem):
    addr = mem.getAddress()
    size = mem.getSize()
    for index in range(size):
        if not ctx.isConcreteMemoryValueDefined(addr+index, 1):
            for r in memoryCache + codeCache:
                if addr+index >= r['start'] and addr+index < r['start'] + r['size']:
                    i = ((addr + index) - r['start'])
                    value = ord(r['memory'][i : i+1])
                    ctx.setConcreteMemoryValue(addr+index, value)
                    #return

    return
# base_adr为load_dump获得的got表所在节的基地址
def makeRelocation(ctx, binary, base_adr, real_base):

    load_list =[]


    # 此处创建虚拟重定位表,针对libc中的库函数
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    # 创建pltgots表，针对自定义so文件中的函数调用
    pltgots=[]
    # 创建重定位表，针对libc中的库函数调用
    relocations = [x for x in binary.pltgot_relocations]
   
    # Perform our own relocations
    if ANALYSE_MODE is X86_32:
        got_table_adr=relocations[0].address # - 0xc 如果是wireshark不能减0xc # GOT[3]及之后的项之后存储的是函数的偏移地址
    else:
        got_table_adr=relocations[0].address - 0x18
    for rel in relocations:
        symbolName = rel.symbol.name
        if IS_LIB:
            '''
                这里其实只有动态链接库需要进行这样的重定位，一般的二进制文件,无论是32还是64其实都是不需要的
            '''
            symbolRelo = rel.address - got_table_adr + base_adr  # 这个算法对libgstflxdec.so动态链接库进行定位是没问题的
            # symbolRelo = rel.address # + real_base #  
        else:
            symbolRelo = rel.address
        flag = 0
        printed = False
        for crel in customRelocation:
            if not printed:
                printed = True
            if symbolName == crel[0]:
                if NOW_ARCH == ARCH.X86:
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.DWORD), crel[2])
                else:
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                flag=1
                break
        if flag==0:
            adr = (ctx.getConcreteMemoryAreaValue(symbolRelo, 8))
            adr = adr[::-1]
            pltgots.append([symbolName,hex(symbolRelo),int(adr.hex(),16)])
    return real_base
    
def initialize():
  # Triton context
    ctx = TritonContext(NOW_ARCH)

    # Set the architecture
    ctx.setArchitecture(NOW_ARCH)

    # Symbolic optimization
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    # Define the Python syntax
    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    # Define internal callbacks.
    ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, Caching)

    # 指定好binary文件
    global binary
    if binary is None: # 如果没有加载过那就进行加载，否则不进行重复操作
        binary = loadBinary(ctx, sys.argv[1])

    entrypoint,base_got_adr,args,code_base_adr, real_base = load_dump(ctx,sys.argv[2],sys.argv[1].split('/')[-1])
    # Perform our own relocations
    real_base = makeRelocation(ctx, binary, base_got_adr, real_base)
    # 这里仅针对gstreamer
    # width_addr = ctx.getConcreteRegisterValue(ctx.registers.r13)+368
    # print(width_addr)
    for mem in TAINTED_MEM:
        for indx in range(abs(TAINTED_MEM[mem])):
            if TAINTED_MEM[mem] >0:
                ctx.taintMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE)) # 将目标位置设置为污染内存
                ctx.symbolizeMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE))
            else:
                ctx.taintMemory(MemoryAccess(mem-indx,CPUSIZE.BYTE)) # 将目标位置设置为污染内存
                ctx.symbolizeMemory(MemoryAccess(mem-indx,CPUSIZE.BYTE))
    '''
        标记受污染的寄存器
    '''
    for per_reg in TAINTED_REG:
        eval("ctx.taintRegister(ctx.registers."+per_reg+")")
        eval("ctx.symbolizeRegister(ctx.registers."+per_reg+")")
    # print(ctx.getTaintedMemory())
    # print("Finish Tainted:",indx)
    return ctx,entrypoint,args,code_base_adr, real_base

'''
    利用类部分
'''
class per_inst_in_stack():
    def __init__(self,
    instruction, # 指令对象
    ins_type, # 指令类型
    taint_rec_dict = {'sa':[],'sm':[],'ta':[]}, # 受污染的目标地址
    ) -> None:
        self.instruction=instruction
        self.ins_type=ins_type
        self.ins_address=str(instruction).split(':')[0] # 这里手动取出内容
        self.taint_rec_dict = taint_rec_dict
    
    '''
        该函数的作用是对
    '''
    def add_taint_flag(self,
                        taint_rec_dict:dict, # 此处是用于记录污染情况的字典
                       ):
        self.taint_rec_dict = taint_rec_dict





class TaintAnalyser():
    def __init__(self,
                 ctx:TritonContext,
                 CodeCache,
                 entry_point=None, # 程序的起始执行地址
                 loop_gate=3,
                 lp_controller=None,
                 tainted_mem = {}, # 该位置用于记录受污染内存的起始位置和长度
                 dataflow_controller=None,
                 ):
        self.CodeCahce = CodeCache # 该结构用于存储当期程序中可执行代码段的内容
        self.tainted_mem = tainted_mem
        self.ctx=ctx
        self.loop_gate=loop_gate
        self.approached_target={} # 该结构用于记录能够到达的gadget
        self.approached_target_by_search=[] # 该结构用于存放在探索中算法识别出的gadget
        self.ast = ctx.getAstContext()
        self.path_list_all=[]
        self.path_list_all_for_emu=[]
        self.taint_record={} # 该数据结构用于记录一个受污染的指令是否被执行太多次
        self.instruct_queue=[]  # 该结构用于缓存十条指令用于进行
        self.instruct_stack=[] # 该结构用于进行gadget的匹配
        self.instruct_taint_dict = [] # 该结构用于记录每条指令所对应的污染情况
        self.gadget_type=[] # 该结构用于记录gadget的类型
        self.gadget_path=[] # 该结构用于记录到达该gadget所走过的路径
        self.gadget_path_jmp=[] # 该结构用于记录jmp指令所在的路径
        self.gadget_loop=[] # 该结构用于记录gadget所处的循环
        self.gadget_control_inst=[] # 该结构用于结构对循环做控制的指令进行记录
        self.gdt_mode_list = [] # 该结构用于进行gdt的收集
        # self.dataflow_controller = dataflow_controller # 该结构用于存储DataFlow对象，用于后续的数据流分析
        self.thread_id_base = 0 # 该结构用于记录当前程序中的起始线程ID
        self.thread_id = '.' # 主线程初始化为点，新线程以线程ID为输出索引
        '''
            mov reg, mem
            mov reg1, reg2
            add reg, 0x1
            inc reg
        '''
        if entry_point is not None:
            self.initial_entry_point=entry_point # 此处用于定义开始分析的指令，可以为空，若为空那起始位置就是ip
        else:
            if ANALYSE_MODE is X86_32:
                self.initial_entry_point=ctx.getConcreteRegisterValue(ctx.registers.eip) # 那就获取当前的ip指针为起始位置
            else:
                self.initial_entry_point=ctx.getConcreteRegisterValue(ctx.registers.rip) # 那就获取当前的ip指针为起始位置
            
        self.finish_tainted=False
        self.last_call_taint=False # 该位置用于解决是否被污染
        self.lp_controller=lp_controller # 这里传入的cdg对象，自己定义的，需要用到的时候直接cdg.cfg即可获取
        self.lp_controller.set_loop_gate(loop_gate)
        self.libc_code_seg = None # {'start':addr1,'size':size} libc的基地址
        self.Target_Binary_Code = None
        # 记录当前程序中libc的范围
        for mem_seg in self.CodeCahce:
            if 'libc-' in os.path.basename(mem_seg['name']):
                self.libc_code_seg = mem_seg
            if fuzz.ratio(os.path.basename(sys.argv[1]), os.path.basename(mem_seg['name'])) >= 90:
                self.Target_Binary_Code = mem_seg
        
        # 安全检查当前程序中的代码段是否找到
        if self.Target_Binary_Code is None:
            raise Exception("Binary Code Seg Not Found ????????")

        # 记录上一次加入的路径情况
        self.last_emuer = None
        # 对循环控制部分代码进行初始化
        self.lp_controller.init_loop_controller()

     
    # 清理当前所以得到的搜索结果，但是不改变配置
    def clear_gadget_rec(self):
        self.path_list_all=[]
        self.path_list_all_for_emu=[]
        self.approached_target_by_search=[] # 该结构用于存放在探索中算法识别出的gadget
        self.gadget_type=[] # 该结构用于记录gadget的类型
        self.gadget_path=[] # 该结构用于记录到达该gadget所走过的路径
        self.gadget_path_jmp=[] # 该结构用于记录jmp指令所在的路径
        self.gadget_loop=[] # 该结构用于记录gadget所处的循环
        self.gadget_control_inst=[] # 该结构用于结构对循环做控制的指令进行记录
    
    # 对当前的上下文内容进行刷新
    def fresh(self):
        self.ctx,self.initial_entry_point,args, base_addr ,real_base=initialize()
        self.lp_controller.clear() # 这里重置其中的内容
        # 这里重置程序中的候选输入
        global std_input
        std_input = deepcopy(back_std_input)
    
    '''
        参数管理函数
    '''
    # 缓存十条指令
    def push_queue_ram(self,inst):
        if len(self.instruct_queue) >= 10:
            self.instruct_queue.pop(0)
        self.instruct_queue.append(inst)   

    # 检查指令中的污染情况
    def check_taint(self,inst,ins_type):
        redict={'sa':[],'sm':[],'ta':[]}
        if type(inst) is int or 'nop' in  str(inst):
            return redict
        if inst.getOperands()[-1].getType() == OPERAND.MEM \
            and inst.getOperands()[0].getType() == OPERAND.REG: # 这里只需要考虑的部分是，当前的两个操作符是什么
            '''
                mov rax, [rbp+rdx+0x10] 从内存取数操作
            ''' 
            for reg in inst.getReadRegisters():
                if self.ctx.isRegisterTainted(reg[0]): # 有点奇怪，
                    redict['sa'].append(str(reg[0])) # 源地址可污染
                    # 此处发现有一个寄存器被污染，那么该地址就是受污染的
            # 检查源地址是否受污染
            target_memory = inst.getOperands()[-1]
            if self.ctx.isMemoryTainted(target_memory):
                mem_size=target_memory.getBitSize()
                redict['sm'].append([target_memory.getAddress(),mem_size]) # 这里记录受污染内存的地址,记录大小
            '''
                检查目标地址
            '''
            if inst.getOperands()[0].getType() == OPERAND.REG:
                my_regs=inst.getWrittenRegisters() # 这里默认对rip进行写，每条指令都会对rip写入，既然目标是reg肯定就只要一个
                if self.ctx.isRegisterTainted(my_regs[-1][0]):
                    redict['ta'].append(str(my_regs[-1][0]))
        elif inst.getOperands()[0].getType() == OPERAND.MEM \
            and inst.getOperands()[-1].getType() == OPERAND.REG: # 如果当前指令是写指令
            '''
                mov [rbp+rdx+0x10],  rax 存入内存
            '''
            # 写入的目标地址
            if inst.getOperands()[0].getType() == OPERAND.MEM:
                base_reg=inst.getOperands()[0].getBaseRegister() # 基地址寄存器
                idx_reg = inst.getOperands()[0].getIndexRegister() # 索引寄存器
                if self.ctx.isRegisterTainted(base_reg) and base_reg.getName() != 'unknown': # 记录受污染的基地址寄存器
                    redict['ta'].append(str(base_reg))
                if self.ctx.isRegisterTainted(idx_reg) and  idx_reg.getName() != 'unknown': # 记录受污染的索引寄存器
                    redict['ta'].append(str(idx_reg))

            # 检查源寄存器数据是否可被污染
            if inst.getOperands()[-1].getType() == OPERAND.REG:
                my_regs=inst.getReadRegisters() # 读取寄存器的内容
                if self.ctx.isRegisterTainted(my_regs[-1][0]): # 前面一个索引到的是写寄存器 [(rax:64 bv[63..0], ref!745), (dl:8 bv[7..0], ((_ extract 7 0) ref!760))]
                    redict['sm'].append(str(my_regs[-1][0])) # 源数据是可以被污染的
        '''
            还有两种情况：
            运算情况是不是也应该归为这一类？？   
        '''
        return redict # 这里返回当前指令的污染情况
    
    # 处理循环问题
    def handle_loop(self,inst, base_addr,pc): # 该函数用于进行对循环的识别和处理操作，包括dispatcher识别和loop跳出代码，同时实现对循环的管理
        # 这里进行循环控制检查
        
        return self.lp_controller.search_cycle(inst, self.check_taint,base_addr) # 检查当前的地址是否是在一个循环内

    # 该位置用于识别指令级的gdt
    def handle_instruct(self,inst,gadget_path, # 该结构记录的是cmp指令
                        current_path,loop): # 该函数用于对输入的指令进行统一的管理
        '''
            该函数的作用是对单个指令的类型进行判断
        '''
        # mov_code=str(inst).split(':')[-1].split()[0] # 取出指令
        mov_code = inst.getDisassembly().replace('rep','').split()[0]
        double_op_list=['sub','add','mul','div'] # 双操作数运算符
        single_op_list = ['inc','dec'] # 单操作符运算
        mov_list = ['mov','movzx','movsx']
        '''
            主要检查三个部分，当前的指令会不会把之前栈中的指令净化,所以无论是不是被污染的指令都要传进来，因为没有被污染的指令可能会净化之前的指令,导致出栈
        '''
        if mov_code=='call': # 处理函数调用的情况
            ins_type=1
        elif mov_code in mov_list or 'stos' in mov_code or 'lods' in mov_code:
            # 这里stos 理解为mov eax，[edi]
            ins_type=0
        elif mov_code in double_op_list: 
            ins_type=2
        elif mov_code in single_op_list: # 如果该操作符是单数运算
            ins_type=3
        elif mov_code == 'ret' or mov_code == 'retn': # 此处是函数执行结束，rax用作返回值
            ins_type = 4 
        else:
            return False
        #  检查单个指令的情况
        return self.handle_ins_stack(inst=inst,ins_type=ins_type,gadget_path=gadget_path,current_path=current_path,loop=loop)
    
    def add_new_gadget(self,t_gadget,loop,gadget_type,gadget_path,current_path):
        '''
            这里增加gadget去重的代码
        '''
        for gdt in self.gdt_mode_list:
            if str(t_gadget[0].instruction) == str(gdt.instructions[0].instruction) and gadget_type == gdt.gadget_type:
                return None
        self.approached_target_by_search.append(t_gadget)
        self.gadget_loop.append(deepcopy(loop))
        self.gadget_type.append(gadget_type)
        self.gadget_path.append(gadget_path)
        self.gadget_path_jmp.append(current_path)
        new_gdt = gadget_mode(
            gadget_type=gadget_type,
            instructions=t_gadget, # 记录当前的指令
            path_to_gadget=gadget_path,
            gadget_loop=loop,
            g_jmp_path=current_path,
            taint_analyser=self
        )
        self.gdt_mode_list.append(new_gdt)
        return new_gdt
    def solve_ret(self,inst_obj,gadget_path,current_path,loop):
        '''
            该函数用于解决遇到ret指令之后rax是受影响的返回值
        '''
        gadget_type='assignment'
        t_gadget=[]
        search_op=['rax']
        pre_len = -1
        while len(t_gadget) > pre_len:
            pre_len = len(t_gadget)
            for per_inst_obj in self.instruct_stack:
                if check_op_in_list(search_op,per_inst_obj.instruction.getOperands()[0]): # 检查当前指令的目标寄存器是不是在目标中
                    if per_inst_obj not in t_gadget:
                        if str(per_inst_obj.instruction).split(":")[-1].split()[0] in  ['sub','add','mul','div']:
                            gadget_type='operating'
                        t_gadget.append(per_inst_obj)
                    if per_inst_obj.instruction.getOperands()[-1].getType()==OPERAND.REG:# 如果源头是寄存器
                        new_op = str(per_inst_obj.instruction.getOperands()[-1]).split(':')[0]
                        if new_op not in search_op:
                            search_op.append(new_op) # 将源头加入到其中
        if len(t_gadget) == 0:
            return
        t_gadget.append(inst_obj)
        if not check_whether_in_gadget(t_gadget,self.approached_target_by_search):
            self.add_new_gadget(t_gadget=t_gadget,loop=loop, gadget_type=gadget_type, gadget_path=gadget_path,current_path=current_path)
            self.approached_target_by_search.append(t_gadget)
            for per_inst_obj in t_gadget:
                if per_inst_obj in self.instruct_stack:
                    self.instruct_stack.remove(per_inst_obj)

    def out_ins_stack(self,inst,gadget_path,current_path,inst_obj=None,loop=None): # 该函数的作用是集合了出栈操作，和gadget的最终生成
        new_gdt = None
        gadget_type='assignment' # 默认是赋值操作
        t_gadget=[] # 用于暂存得到的gadget状态
        source_oprand=[str(inst.getOperands()[-1]).split(':')[0]] # 此处获取源操作数
        pre_len = -1
        while len(t_gadget) > pre_len:
            pre_len = len(t_gadget)
            for per_inst_obj in self.instruct_stack:
                if check_op_in_list(source_oprand,per_inst_obj.instruction.getOperands()[0]): # 检查当前指令的目标寄存器是不是在目标中
                    if per_inst_obj not in t_gadget:
                        if str(per_inst_obj.instruction).split(":")[-1].split()[0] in  ['sub','add','mul','div']:
                            gadget_type='operating gadget'
                        t_gadget.append(per_inst_obj)
                    if per_inst_obj.instruction.getOperands()[-1].getType()==OPERAND.REG:# 如果源头是寄存器
                        new_op = str(per_inst_obj.instruction.getOperands()[-1]).split(':')[0]
                        if new_op not in source_oprand:
                            source_oprand.append(new_op) # 将源头加入到其中
        t_gadget.reverse() # 这里要不直接换成排序？？
        # t_gadget = sort_gadget(t_gadget)
        if  inst_obj is not None:
            t_gadget.append(inst_obj) # 由于本身写回操作也属于gadget中的一环,这里对gadget写回进行操作
        if not check_whether_in_gadget(t_gadget,self.approached_target_by_search) and len(t_gadget) !=0\
            and len(source_oprand) !=0 : # 如果是单个指令的mov则不做任何操作，可能只是目标地址受污染
            self.approached_target_by_search.append(t_gadget) # 放入此所有能搜索到的gadget列表中存储
            if gadget_type == 'assignment': # 检查当前的gadget属于什么类型
                '''
                    如果是赋值语句，则有可能是函数的调用过程，检查当前的
                '''
                start_tag=False
                for ram_ins in self.instruct_queue: # 检查当前的指令缓存
                    if not start_tag:
                        if str(t_gadget[0].instruction)== str(ram_ins):
                            start_tag = True
                    if start_tag:
                        if str(ram_ins).split(":")[-1].split()[0] == 'call':
                            gadget_type+='--->assigment variable call'
                            break
                        if str(t_gadget[-1].instruction)== str(ram_ins): # 检查完就结束了
                            break
            new_gadget = self.add_new_gadget(t_gadget=t_gadget,loop=loop, gadget_type=gadget_type, gadget_path=gadget_path,current_path=current_path)
            return new_gadget
        
        # 这里要出栈的吧，不然后面不是好多重复的gadget
        for per_inst_obj in t_gadget:
            if per_inst_obj in self.instruct_stack:
                self.instruct_stack.remove(per_inst_obj) # 这里似乎是有重复的指令在里面导致的问题
        return new_gdt


    def clear_ins_stack(self,target_op,is_tained=False,inst_obj=None):# 该函数的作用是根据目的操作数，找到所有该目的操作数的指令进行清除
        t_delete=[]
        for per_inst_obj in self.instruct_stack:
            '''
                这里遇到一个问题，自己不能净化自己
            '''
            if  is_op_equal(per_inst_obj.instruction.getOperands()[0],target_op, normal=False):
                t_delete.append(per_inst_obj)
            if is_op_equal(per_inst_obj.instruction.getOperands()[-1],target_op, normal=False): # 这里源头和目的都可以清空了，因为操作不保存也不会有意义
                t_delete.append(per_inst_obj)
        for per_inst_obj in t_delete:
            try:
                self.instruct_stack.remove(per_inst_obj) # 这里似乎是有重复的指令在里面导致的问题
            except:
                pass
        # 此处是净化了，但需要替换
        if is_tained:
            self.instruct_stack.append(inst_obj)
    '''
        产生一个可用gadget
    '''

    # 该函数用于处理栈中的指令
    def handle_ins_stack(self,inst,ins_type,gadget_path,current_path,loop):
        '''
            该位置并不会对当前的指令是否污染做判断，而是直接进行类型的构建
            有以下问题暂时没有解决 inc [cx] 是否视为尬的高铁

        '''
        ins_obj=per_inst_in_stack(instruction=inst,ins_type=ins_type) # 此处创建指令对象
        '''
            这里首先并不进行任何的污染检查，由checktaint函数来返回检查情况
        '''
        redict={'sa':[],'sm':[],'ta':[]}
        # 首先判断当前的指令是否被污染，如果是没有被污染的指令，那么只有可能会对栈中指令进行净化
        if ins_type == 4:
            '''
                此处用于解决函数返回，影响留存在rax中的情况
            '''
            return None
            # return self.solve_ret(ins_obj,gadget_path,current_path,loop)
        '''
            如果此处本身就没有被污染，那么就考虑其是否是取地址类型
        '''
        if not inst.isTainted():
            if ins_type==0:# 如果是mov指令，或者lods和stos这类内存操作指令
                '''
                    获取当前指令的目的操作数，查看与栈中的目的操作数有无重合的部分
                '''
                if 'lods' in inst.getDisassembly():
                    # 这里的load会产生值的覆盖
                    if NOW_ARCH is ARCH.X86_64:
                        target_op = self.ctx.registers.rax
                    else:
                        target_op = self.ctx.registers.eax
                    self.clear_ins_stack(target_op)
                elif 'stos' in inst.getDisassembly():
                    pass
                elif inst.isMemoryRead() and len(inst.getStoreAccess()) == 0 and len(inst.getReadRegisters())!=0: # 解引用操作
                    # 检查执行之前是不是污染的
                    if self.last_taint_state[str(inst.getReadRegisters()[-1][0]).split(':')[0]]:
                        # print("Tainted  Reg!")
                        # 污染以此作为索引，写入的寄存器
                        self.ctx.taintRegister(inst.getWrittenRegisters()[0][0])
                        taint_dict =self.check_taint(inst,ins_type)
                        ins_obj.add_taint_flag(taint_dict) # 添加污染标记
                        self.instruct_stack.append(ins_obj) # 此处是mov指令，直接入栈,作为开头的地址
                        self.instruct_taint_dict.append(taint_dict) # 记录当前指令的污染状况
                        print('\033[30m[+] ADD TAINT ↑ \033[0m')
                else:
                    target_op=inst.getOperands()[0] # 这里获取目的操作数    
                    self.clear_ins_stack(target_op)

            elif ins_type == 3: # 如果本身是一个单运算符
                '''
                    此处只针对inc [mem] 的情况进行检查
                '''
                if inst.getOperands()[-1].getType() == OPERAND.MEM: # 如果对应的操作符是内存
                    if not check_whether_in_gadget([ins_obj],self.approached_target_by_search):
                        base_reg=inst.getOperands()[0].getBaseRegister() # 基地址寄存器
                        idx_reg = inst.getOperands()[0].getIndexRegister() # 索引寄存器
                        '''
                            记录该指令的受污染情况
                        '''
                        if self.ctx.isRegisterTainted(base_reg) and base_reg.getName() != 'unknown': # 记录受污染的基地址寄存器
                            redict['ta'].append(base_reg)
                        if self.ctx.isRegisterTainted(idx_reg) and  idx_reg.getName() != 'unknown': # 记录受污染的索引寄存器
                            redict['ta'].append(idx_reg)
                        ins_obj.add_taint_flag(redict)
                    # 对受污染的内存自加操作本身就是gadget
                        new_gdt = self.add_new_gadget(t_gadget=[ins_obj],loop=loop, gadget_type='operating', gadget_path=gadget_path,current_path=current_path)
                        return new_gdt
            return
        
        if len(self.instruct_stack) == 0 and ins_type==0:
            # 检查当前load指令的，相当于mov eax, [edi]
            if 'lods' in inst.getDisassembly():
                pass


            taint_dict =self.check_taint(inst,ins_type) 
            ins_obj.add_taint_flag(taint_dict) # 添加污染标记
            self.instruct_stack.append(ins_obj) # 此处是mov指令，直接入栈,作为开头的地址
            self.instruct_taint_dict.append(taint_dict) # 记录当前指令的污染状况
            return 
        elif len(self.instruct_stack) !=0 and ins_type==0: # 如果这个时候栈不为空，并且有赋值语句
            taint_dict =self.check_taint(inst,ins_type) 
            ins_obj.add_taint_flag(taint_dict) 
            if inst.getOperands()[0].getType() == OPERAND.MEM:
                self.clear_ins_stack(inst.getOperands()[0])
                '''
                    mov mem, reg
                '''
                return self.out_ins_stack(inst,gadget_path,current_path,inst_obj=ins_obj,loop=loop) # 如果这里是写回操作,即可生成gadget
            elif inst.getOperands()[0].getType() == OPERAND.REG \
                and inst.getOperands()[-1].getType() == OPERAND.REG:
                ''' 
                    mov reg1, reg2 finsih
                '''
                if ins_obj not in self.instruct_stack:
                    self.instruct_stack.append(ins_obj)
                return None
            elif inst.getOperands()[0].getType() == OPERAND.REG \
                and inst.getOperands()[-1].getType() == OPERAND.MEM:
                self.clear_ins_stack(inst.getOperands()[0],inst_obj=ins_obj)
                # 此处是取数操作，有两种情况取a，取b，取出污染内存的值加到某个值上，也就是进行引用，
                '''
                    mov reg, mem
                '''
                if ins_obj not in self.instruct_stack:
                        self.instruct_stack.append(ins_obj) # 其实这里就只能是一个中间操作，只能说在最后出栈的时候，把相关的内容都出栈
                return None
        elif ins_type==2: # 如果当前是双操作数
            taint_dict =self.check_taint(inst,ins_type) 
            ins_obj.add_taint_flag(taint_dict) 
            if inst.getOperands()[-1].getType()==OPERAND.IMM:
                # 如果获取到的操作数是立即数
                if inst.getOperands()[0].getType()==OPERAND.REG: # 如果是对寄存器操作则要去栈里找指令
                    if ins_obj not in self.instruct_stack:
                        self.instruct_stack.append(ins_obj) # 不必对先前内容进行任何检查操作，直接入栈即可，被污染了肯定是前面有的
                        return False
                elif inst.getOperands()[0].getType()==OPERAND.MEM: # 如果目标操作数是内存
                    '''
                        这其实这里条指令就是一个gadget
                    '''
                    if not check_whether_in_gadget([ins_obj],self.approached_target_by_search):
                        self.add_new_gadget(t_gadget=[ins_obj],loop=loop, gadget_type='operating', gadget_path=gadget_path,current_path=current_path)
                        return new_gdt
            elif inst.getOperands()[-1].getType()==OPERAND.REG\
                and inst.getOperands()[0].getType()==OPERAND.REG:
                '''
                    add reg1, reg2 从两个内存地址中取数相加的情况
                '''
                self.instruct_stack.append(ins_obj)  # TODO  这里先直接入栈看一下,大概率是会有问题
                return None
            elif inst.getOperands()[-1].getType()==OPERAND.MEM\
                and inst.getOperands()[0].getType()==OPERAND.REG:
                    '''
                        add reg, mem
                        本质上来说就是一个解引用gdt后进行了一次加法
                        mov tmp , mem
                        add reg, tmp
                    '''
                    self.instruct_stack.append(ins_obj)  # 直接入栈
            elif inst.getOperands()[-1].getType()==OPERAND.REG\
                and inst.getOperands()[0].getType()==OPERAND.MEM:
                '''
                    add mem, reg 好像暂时没有遇到过这类情况
                '''
                return self.out_ins_stack(inst,ins_obj,current_path,loop=loop)
        # 对当前这种情况采用单独处理
        elif len(self.instruct_stack) !=0 and ins_type==3: # 如果当前是单操作数
            # 单操作数
            if inst.getOperands()[-1].getType()==OPERAND.REG:
                redict['sm'].append(inst.getOperands()[-1]) # 直接将其放入到sm对应的字典中
                ins_obj.add_taint_flag(redict) 
                if ins_obj not in self.instruct_stack:
                        self.instruct_stack.append(ins_obj) # 此处直接压栈即可,肯定是对栈内某个寄存做的操作
                return None
            else:
                # 检查目标内存，如果仅仅是目标地址被污染，Triton不将其视为被污染
                target_memory = inst.getOperands()[-1]
                if self.ctx.isMemoryTainted(target_memory):
                    mem_size=target_memory.getBitSize()
                    redict['sm'].append([target_memory.getAddress(),mem_size]) # 这里记录受污染内存的地址,记录大小
                # 这里加的如到
                ins_obj.add_taint_flag(redict) 
                if not check_whether_in_gadget([ins_obj],self.approached_target_by_search):
                    new_gdt = self.add_new_gadget(t_gadget=[ins_obj],loop=loop, gadget_type='operating', gadget_path=gadget_path,current_path=current_path)
                    return new_gdt

    def hookingHandler(self,ctx,tainted_flag,symbol_mem_map, loop=None, gadget_path=None, current_path = None, instruction =None): # 第二个参数用于标记当前的库函数调用是否是被污染的
        if ANALYSE_MODE is X86_32:
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
        else:
            pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
        head_inst = [] # 该结构用于记录当前libc gadget的寄存器赋值语句
        is_gadget = None
        hooking_flag = False
        for rel in customRelocation:
            if rel[2] == pc: # 这里取出plt表中的内容，检查其指向的地址是否在库函数中
                hooking_flag = True
                global GadgetFunc2Addr
                # 检查当前程序中的
                if pc in list(GadgetFunc2Addr.values()):
                    # 这里是64位程序中的gadget识别，检查相关寄存器的值是否受污染
                    if NOW_ARCH is ARCH.X86_64:                    
                        self.instruct_queue.reverse()
                        for inst in self.instruct_queue:
                            if 'call' in str(inst) or 'jmp' in str(inst):
                                call_instruction = inst
                                break
                        # print("call_instruction:%s"%str(call_instruction))
                        ins_obj=per_inst_in_stack(instruction=call_instruction,ins_type=1) #此处创建指令对象
                        '''
                            这里需要
                        '''
                        got_rdi = False
                        got_rsi = False
                        got_rdx = False
                        if 'recv' == rel[0]:
                            for inst in self.instruct_queue:
                                if len(inst.getOperands()) in [0, 1]: # 64位程序传参不必关心这一部分
                                    continue
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rsi') and not got_rsi: # and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rsi = True
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rdx') and not got_rdx: #  and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rdx = True
                            self.instruct_queue.reverse()          
                            if ctx.isRegisterTainted(ctx.registers.rsi):
                                is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='RECV_libc', gadget_path=gadget_path,current_path=current_path)
                                print("RECV gadget:%s"%(str(call_instruction)))
                        elif 'sudo_memset_s' == rel[0]:
                            print("GOT! sudo_memset_s")
                            for inst in self.instruct_queue:
                                if len(inst.getOperands()) in [0, 1]: # 64位程序传参不必关心这一部分
                                    continue
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rdi') and not got_rdi: # and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rdi = True
                            self.instruct_queue.reverse()          
                            if ctx.isRegisterTainted(ctx.registers.rdi):
                                is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='memset_libc', gadget_path=gadget_path,current_path=current_path)
                                print("memset gadget:%s"%(str(call_instruction)))
                            
                        else:
                            for inst in self.instruct_queue:
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rdx') and not got_rdx: #  and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rdx = True
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rdi') and not got_rdi: #  and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rdi = True
                                if is_op_equal(str(inst.getOperands()[0]).split(':')[0], 'rsi') and not got_rsi: # and (str(inst.getOperands()[0]).split(':')[0] != str(inst.getOperands()[-1]).split(':')[0]):
                                    head_inst.append(per_inst_in_stack(instruction=inst,ins_type=-1))
                                    got_rsi = True
                            self.instruct_queue.reverse()          
                            if ctx.isRegisterTainted(ctx.registers.rdi):
                                if ctx.isRegisterTainted(ctx.registers.rsi):
                                    # 这里rdi和rsi寄存器被污染，arbitrary copygadget。
                                    is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMCgadget_libc', gadget_path=gadget_path,current_path=current_path)
                                    print("arbitrary copygadget:%s"%(str(call_instruction)))
                                else:
                                    # 这里rdi寄存器被污染，arbitrary writegadget。
                                    print("arbitrary writegadget%s"%(str(call_instruction)))
                                    is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMWgadget_libc', gadget_path=gadget_path,current_path=current_path)
                            elif ctx.isRegisterTainted(ctx.registers.rsi):
                                # self.approached_target_by_search.append([ins_obj]) # 这里rsi寄存器被污染，arbitrary readgadget。
                                print("arbitrary readgadget%s"%(str(call_instruction)))
                                is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMRgadget_libc', gadget_path=gadget_path,current_path=current_path)
                            
                            elif ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi),CPUSIZE.DWORD)):
                                '''
                                    也有可能寄存器的值是没有被污染的，但是其指向的内存是被污染的，类似用户输入这种情况
                                '''
                                # self.approached_target_by_search.append([ins_obj]) # 这里rsi寄存器指向的内存被污染，state readgadget。
                                print("state readgadget%s"%(str(call_instruction)))
                                # self.gadget_type.append('state target read gadget')
                                is_gadget = self.add_new_gadget(t_gadget=head_inst + [ins_obj],loop=loop, gadget_type='state target read gadget_libc', gadget_path=gadget_path,current_path=current_path)
                    else:
                        '''
                            这里向上遍历指令找到距离最近的三个push
                        '''
                        self.instruct_queue.reverse()
                        counter_push = 0
                        for t_inst in self.instruct_queue:
                            if 'push' in str(t_inst) or '[esp' in str(t_inst):
                                head_inst.append(per_inst_in_stack(instruction=t_inst,ins_type=-1))
                                counter_push += 1
                            if counter_push >= 3:
                                # 只取出最近的三条push指令
                                break
                        for inst in self.instruct_queue:
                            if 'call' in str(inst) or 'jmp' in str(inst):
                                call_instruction = inst
                                break
                        # print("call_instruction:%s"%str(call_instruction))
                        ins_obj=per_inst_in_stack(instruction=call_instruction,ins_type=1) #此处创建指令对象
                        self.instruct_queue.reverse()
                        
                        # 32位gadget识别
                        if ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4):
                            if ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8):
                                is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMCgadget_libc32', gadget_path=gadget_path,current_path=current_path)
                                print("arbitrary copygadget:%s"%(str(call_instruction)))
                            else:
                                print("arbitrary writegadget%s"%(str(call_instruction)))
                                is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMWgadget_libc32', gadget_path=gadget_path,current_path=current_path)
                        elif ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8):  # 检查当前程序中的
                            print("arbitrary readgadget%s"%(str(call_instruction)))
                            is_gadget = self.add_new_gadget(t_gadget=head_inst+[ins_obj],loop=loop, gadget_type='AMRgadget_libc32', gadget_path=gadget_path,current_path=current_path)
                        elif ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)):
                            print("state readgadget%s"%(str(call_instruction)))
                            is_gadget = self.add_new_gadget(t_gadget=head_inst + [ins_obj],loop=loop, gadget_type='state target read gadget_libc32', gadget_path=gadget_path,current_path=current_path)

                # Emulate the routine and the return value
                tmp= rel[1](ctx,self.last_call_taint,symbol_mem_map) # 这里模拟每一个库函数的执行过程
                self.last_call_taint=False
                try:
                    ret_value=tmp[0]
                    ctx=tmp[1]
                except:
                    ret_value=tmp
                if NOW_ARCH is ARCH.X86:
                    ctx.setConcreteRegisterValue(ctx.registers.eax, ret_value)
                    # Get the return address
                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp), CPUSIZE.DWORD))

                    # Hijack RIP to skip the call
                    ctx.setConcreteRegisterValue(ctx.registers.eip, ret_addr)

                    # Restore RSP (simulate the ret)
                    ctx.setConcreteRegisterValue(ctx.registers.esp, ctx.getConcreteRegisterValue(ctx.registers.esp)+CPUSIZE.DWORD)
                else:
                    # # 这里如果是64位就设置返回值给rax
                    # ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)

                        # Get the return address
                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))

                    # Hijack RIP to skip the call
                    ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)

                    # Restore RSP (simulate the ret)
                    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
                if ret_value == 0xdeadbeef:
                    '''
                        这里表示抓到栈，保护检查，没有办法正常通过
                        - 遍历指令序列回到之前的跳转指令部分
                    '''
                    self.instruct_queue.reverse()
                    next_target = None
                    jmp_target_addr = None
                    jumped = False
                    for inst_idx in range(len(self.instruct_queue)):
                        if next_target is None:
                            # 先寻找是哪个指令造成的check fail的跳转
                            if self.instruct_queue[inst_idx].isBranch() and 'jmp' not in str(self.instruct_queue[inst_idx]):
                                next_target = self.instruct_queue[inst_idx].getNextAddress()
                                jmp_target_addr = int(get_jump_target(ctx,self.instruct_queue[inst_idx]), 16)
                                # 寻找是否跳转成功
                                if self.instruct_queue[inst_idx - 1].getAddress() == jmp_target_addr:
                                    jumped = True
                                break
                    self.instruct_queue.reverse()
                    if jumped:
                        if NOW_ARCH is ARCH.X86:
                            # 如果是jmp成功导致的那就返回不成功的
                            ctx.setConcreteRegisterValue(ctx.registers.eip, next_target)
                        else:
                            ctx.setConcreteRegisterValue(ctx.registers.rip, next_target)
                    else:
                        if NOW_ARCH is ARCH.X86:
                            # 如果是跳转不成功导致的，就直接转到跳转目标上去
                            ctx.setConcreteRegisterValue(ctx.registers.eip, jmp_target_addr)
                        else:
                            ctx.setConcreteRegisterValue(ctx.registers.rip, jmp_target_addr)
                    # 表示检测
        return ctx, is_gadget, hooking_flag
    
    def pop_stack(self):
        if NOW_ARCH is ARCH.X86:
                # 获取当前程序中的返回地址
            ret_addr = self.ctx.getConcreteMemoryValue(MemoryAccess(self.ctx.getConcreteRegisterValue(self.ctx.registers.esp), CPUSIZE.DWORD))
            self.ctx.setConcreteRegisterValue(self.ctx.registers.esp, self.ctx.getConcreteRegisterValue(self.ctx.registers.esp) + CPUSIZE.DWORD)
        else:
            # 获取当前程序中的返回地址
            ret_addr = self.ctx.getConcreteMemoryValue(MemoryAccess(self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp), CPUSIZE.QWORD))
            self.ctx.setConcreteRegisterValue(self.ctx.registers.rsp, self.ctx.getConcreteRegisterValue(self.ctx.registers.rsp) + CPUSIZE.QWORD)
        return ret_addr

        # 该函数用于检查当前函数中存在的
    def check_repeat_instruct(self):
        if len(self.instruct_queue) == 1:
            return False
        str_inst = [str(inst) for inst in self.instruct_queue]
        if (len(set(str_inst)) != len(self.instruct_queue) and len(set(str_inst))==1):
            if 'rep' in list(set(str_inst))[0]:
                return False
            return True
        return False
    def first_run(self,
                    start_address=None,
                    exit_address=None, # 结束分析的位置
                    # 下面是本次执行的一些控制开关
                    is_search_path = True, # 控制当前是否进行路径的探索
                    is_search_gdt = True,  # 控制当前是否进行gdt搜索
                    # 设置特定任务的开关
                    record_model_list=[], # 该结构用于存储操作的函数
                    slow_run = True, # 设置为False时忽略对新路径的探索
                    new_path_map = None,
                    angr_cfg = None,
                    switch_node = None,
                    ):
        '''
            该函数仅用于程序的首次执行操作
        '''
        my_saver = inst_saver() # 用于缓存当前程序走过路径上的指令
        loop = [] # 该位置用于记录当前gadget所处的dispatcher是哪一个,dispatcher 可能有多个
        pc=start_address if start_address is not None else self.initial_entry_point
        pc_list={}# 该变量用于记录路径上所有受影响的跳转指令及其选择
        pc_list_for_emu={} # 这个变量用于记录跳转指令前的判断指令
        self.last_taint_state = get_taint_state(self.ctx)
        main_switch_node = [] # 该结构用于记录本次运行过程中所有走过的switch节点 [{instructio:choice}]
        count_inst = 0 # 用于记录当前指令的执行次数
        while pc:
            # 检查当前是否跑出程序,如果跑出当前程序就直接退出，或者获取ret值
            if not (pc < self.Target_Binary_Code['start'] + self.Target_Binary_Code['size'] and pc >self.Target_Binary_Code['start']):
                print("[debug] jump_out_of_range:",hex(pc))
                if 'ret' in str(instruction):
                    print("Return Invalid Address!")
                    showDebugInfo(self.ctx)
                    # 检查当前程序中的寄存器
                    try:
                        if self.ctx.isRegisterTainted(self.ctx.registers.rip):
                            # 检查当前的寄存器是否污染
                            print("ROP FOUND But Invalid Address!")
                    except:
                        if self.ctx.isRegisterTainted(self.ctx.registers.eip):
                            # 检查当前的寄存器是否污染
                            print("ROP FOUND But Invalid Address!")
                # 如果这里是call出去的，那么说明还能回来
                if 'call' in str(self.instruct_queue[-1]):
                    # 那就直接pop栈然后返回
                    pc = self.pop_stack()
                else:
                    break
            if pc == 0x804BC8B:
                print("GOT!")
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16) # 这里是取出其中的操作码          
            instruction = Instruction(pc, opcode)
            # 缓存当前的指令
            my_saver.solve(hex(pc))
            try:
                self.ctx.processing(instruction)
            except:
                print("[debug] Illegal inst",hex(pc))
                break
            pre_pc = instruction.getNextAddress()
            count_inst += 1
            if 'ret' in str(instruction) or 'leave' in str(instruction):
                self.last_call_taint=False
            if pc == 0x07FFFE6281B48:
                print("GOT BRANCH")
            if pc == 0x5b9af9:
                print("GOT BRANCH")
            # 打印
            RESULT_log(str(instruction),instruction.isTainted(),self.thread_id)
            # print(pc,end=',\n')
            # DEBUG点
            if instruction.getAddress() in list(DEBUG_ADDR.keys()) and slow_run:
                print("Now Break at:", DEBUG_ADDR[instruction.getAddress()])
                showDebugInfo(self.ctx)
                print('IsMemoryRead:',instruction.isMemoryRead())
                print('Operands:',instruction.getOperands())
                print('ReadRegisters:',instruction.getReadRegisters())
                print('StoreAccess:',instruction.getStoreAccess())
                print('LoadAccess:',instruction.getLoadAccess())
                print('WriteRegister:',instruction.getWrittenRegisters())
            # 强调试模式
            if HARD_DEBUG:
                showDebugInfo(self.ctx)
            
            new_gadget = None
            # 处理当前在循环中的状态
            ret_val,loop_flag = self.handle_loop(instruction,BASE_ADDR,pc)
            # 更新全局参数
            if loop_flag not in [-2,1] and ret_val is not None:
                loop = ret_val
            
            if instruction.getType() == OPCODE.X86.HLT or pc == exit_address or self.check_repeat_instruct():
                break
            
            # 检查当前是否进行了系统调用
            self.ctx,is_new_libc_gadget,hooking_flag=self.hookingHandler(self.ctx,self.last_call_taint,None,loop,pc_list_for_emu,pc_list,instruction)
            # 正常获取下一条指令
            if ANALYSE_MODE is X86_32:
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
            else:
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
            '''
                自定义函数处理
            '''
            # 后面有新的部分
            mode_generate_path = None
            mode_generate_path_cmp = None

            if is_search_gdt:
                new_gadget = self.handle_instruct(instruction,mode_generate_path_cmp,mode_generate_path,loop)
            '''
                这里做实验记录
            '''
            # if new_gadget not in [None,False]:
            #     print("got")
            if new_gadget not in [None,False]:
                my_saver.finish_saveG1(self.ctx, new_gadget, file_name=sys.argv[1].split('/')[-1]+".gdt",angr_proj=ANGR_PROJ,code_base = BASE_ADDR)
            if is_new_libc_gadget not in [None,False]:
                my_saver.finish_saveG1(self.ctx, is_new_libc_gadget, file_name=sys.argv[1].split('/')[-1]+".gdt",angr_proj=ANGR_PROJ,code_base = BASE_ADDR)
            
            '''
                实验记录
            '''
            for solve_model in record_model_list:
                if is_new_libc_gadget is not None and (new_gadget is None or new_gadget is False):
                    new_gadget = is_new_libc_gadget # 这里始终返回的是一个gadget_mode对象
                ret=solve_model.solve(instruction,self.ctx,hooking_flag, new_gadget) # 将所有的操作都打包到一个函数中
                try:
                    # 此处开始进行
                    mode_generate_path,mode_generate_path_cmp = solve_model.get_main_path()
                except:
                    pass
                try:
                    # 这里获取本次产生的新路径，这里获得的是两个列表
                    new_cmp_path , new_jmp_path = solve_model.get_current_new()
                    # 获取完成后，清理缓存
                    solve_model.clean()
                except:
                    pass
                if ret == 1: # 如果当前的处理函数的返回结果是1，则证明目前条件已经足以让程序退出
                    return
                elif type(ret) == dict and new_gadget is not None and new_gadget is not False: # 如果这里返回的是一个字典，则表明当前再获得的gdt需要载入range属性
                    self.gdt_mode_list[-1].taint_range = ret # 这里向最新加入的gdt装载相应指令的污染情况
            # 这里开始进行gadget的检查
            # 这里需要做一个标识
            
            # 如果当前对应的gadget既不是None也不是False，那说明是真的产生了一个gadget
            if new_gadget is not None and new_gadget is not False:
                # 这里肯定是取出最后一个gadget添加路径
                self.gadget_path[-1] = mode_generate_path_cmp
                self.gadget_path_jmp[-1] = mode_generate_path
                self.gdt_mode_list[-1].g_jmp_path = mode_generate_path
                self.gdt_mode_list[-1].path_to_gadget = mode_generate_path_cmp
            '''
                符号执行部分
                -   遇到符号化分支的时候再进行求解操作
                -   如果是遇到一个分支就开启一个新的上下文状态ctx
            '''
            if len(self.instruct_queue) != 0 and instruction.isSymbolized():
                if str(self.path_list_all) not in Thread_pathes:
                    next_op = None
                    ck_flag = False
                    switch_target_list = None
                    ctx_list=[]
                    new_ctx = None
                    if 'cmp' in str(instruction):
                        new_ctx,new_initial_entry_point,args, new_base_addr ,real_base= initialize()
                        next_opcode = self.ctx.getConcreteMemoryAreaValue(pre_pc, 16)
                        # 下一个操作
                        next_op = get_next_inst_oprand(instruction,next_opcode)
                        ck_flag = True
                    elif 'jmp' in str(instruction):
                        for path_ctrler in record_model_list:
                            try:
                                switch_target_list = path_ctrler.getSwitchMode(instruction)
                                break
                            except:
                                continue
                        # 这里要生成n-1个状态， 自己本身的状态不需要生成
                        if switch_target_list is not None:
                            for i in range(len(switch_target_list)-1): 
                                new_ctx,new_initial_entry_point,args, new_base_addr ,real_base = initialize()
                                ctx_list.append(new_ctx)

                            ck_flag = True
                    
                    if ck_flag:
                        new_ctx = slight_slight_touch(instruction=instruction,ctx = self.ctx, new_ctx=new_ctx, next_op = next_op, switch_target=switch_target_list,ctx_list=ctx_list)
                        if new_ctx is not None:
                            if type(new_ctx) is list:
                                # switch 结束时返回的结果
                                for per_target, per_new_ctx in zip(switch_target_list,new_ctx):
                                    if (instruction.getAddress(), per_target) in searched_branched:
                                        # 如果这里已经记录过了就继续
                                        continue
                                    new_emuer = fast_emuer(
                                    new_ctx = per_new_ctx,
                                    new_entry_point=new_initial_entry_point,
                                    new_base_addr= new_base_addr,
                                    thread_id=str(self.thread_id_base),
                                    current_branch=(instruction.getAddress(), per_target), #  这里传入的是要进行跳转的目标地址
                                    switch_node = deepcopy(main_switch_node)+[{str(instruction):per_target}] # 后面可以通过检查该变量是否为None判断路径情况
                                    )
                                    current_rank = get_rank_from_map(BRANCH_MAP,instruction.getAddress(),per_target,self.ctx,BASE_ADDR)
                                    Thread_pathes.append(deepcopy(str(self.path_list_all)))
                                    # 这里记录新的id与模拟器之间的映射关系
                                    with counter_lock:
                                        global emuer_pool
                                        # 第二个位置是rank，但此时还不知道下一步的分支走向
                                        # if (instruction.getAddress(), per_target) not in searched_branched:
                                        emuer_pool[(self.thread_id_base,current_rank)]=new_emuer
                                        self.thread_id_base += 1
                                        searched_branched.append((instruction.getAddress(), per_target) )
                                # 这里设置成上一次加入路径的数量
                                self.last_emuer = None
                            else:
                                # 如果这里是一般分支的返回结果
                                new_emuer = fast_emuer(
                                    new_ctx = new_ctx,
                                    new_entry_point=new_initial_entry_point,
                                    new_base_addr= new_base_addr,
                                    thread_id=str(self.thread_id_base),
                                    current_branch=None, #  
                                    switch_node = deepcopy(main_switch_node)
                                    )
                                Thread_pathes.append(deepcopy(str(self.path_list_all)))
                                # 上一次只加入了一个路径
                                self.last_emuer = new_emuer
                        else:
                            # 这里，当前路径不可解则直接设置其为None
                            self.last_emuer = None    
                        
            '''
                记录main switch node
            '''
            if 'jmp rax' in str(instruction):
                print("got jmp rax")
            if len(self.instruct_queue) != 0:
                if self.instruct_queue[-1].isBranch() and 'jmp' in str(self.instruct_queue[-1]) and self.instruct_queue[-1].getOperands()[-1].getType() == OPERAND.REG:
                    main_switch_node.append({str(self.instruct_queue[-1]):instruction.getAddress()})
                    
            '''
                路径约束收集，收集所有的受污染节点
            '''
            if instruction.isTainted() and is_search_path: # 只有被污染的跳转指令才会被当做可控路径，这里只有确定进行路径探索才会做该操作
                jmp_code=str(instruction).split(":")[-1].split()[0]
                if instruction.isBranch() and jmp_code != 'jmp': # 符号指针的问题暂时不做处理
                    jump_tartget=get_jump_target(self.ctx,instruction)
                    if instruction.getAddress() not in pc_list:
                        if str(hex(pc))==jump_tartget:
                                # 此处表明跳转成功,那就把之前的下一条指令得到,这里修改一下不只是记录跳转指令应该记录两条，跳转和判断指令
                            pc_list[instruction.getAddress()]=instruction
                            pc_list_for_emu[self.instruct_queue[-1].getAddress()]=True

                            if self.last_emuer != None:
                                # 最后一个
                                self.last_emuer.current_branch = (instruction.getAddress(), instruction.getAddress()+ instruction.getSize())
                                current_rank = get_rank_from_map(BRANCH_MAP,instruction.getAddress(),instruction.getAddress()+ instruction.getSize(),self.ctx,BASE_ADDR)
                                with counter_lock:
                                    # 第二个位置是rank，但此时还不知道下一步的分支走向
                                    emuer_pool[(self.thread_id_base,current_rank)]=self.last_emuer
                                    self.thread_id_base += 1
                                self.last_emuer = None
                        else:
                            pc_list[instruction.getAddress()]=instruction
                            pc_list_for_emu[self.instruct_queue[-1].getAddress()]=False
                            if self.last_emuer != None:
                                self.last_emuer.current_branch = (instruction.getAddress(), jump_tartget)
                                current_rank = get_rank_from_map(BRANCH_MAP,instruction.getAddress(),instruction.getAddress()+ instruction.getSize(),self.ctx,BASE_ADDR)
                                with counter_lock:
                                    # 第二个位置是rank，但此时还不知道下一步的分支走向
                                    emuer_pool[(self.thread_id_base,current_rank)]=self.last_emuer
                                    self.thread_id_base += 1
                                self.last_emuer = None
                        # 加入到路径列表中
                    if pc_list not in self.path_list_all:
                        self.path_list_all.append(pc_list.copy())
                    if pc_list_for_emu not in self.path_list_all_for_emu:
                        self.path_list_all_for_emu.append(deepcopy(pc_list_for_emu))
                elif jmp_code == 'jmp' and instruction.getOperands()[0].getType() == OPERAND.REG:
                    pass
            
            self.last_taint_state = get_taint_state(self.ctx)
            '''
                此处对指令做缓存
            '''
            self.push_queue_ram(instruction) # 这里对指令进行缓存
            if loop_flag == -1:
                if len(ret_val[0][-1].break_edges) != 0:
                    if len(ret_val[0][-1].break_edges) > 1:
                        # 这里采用随机探索的方式选择一个break_edge、
                        pc = ret_val[0][-1].break_edges[-1][-1].addr + BASE_ADDR - ANGR_BASE
                        # pc = ret_val[0][-1].break_edges[random.randint(0, len(ret_val[0][-1].break_edges)-1)][-1].addr + BASE_ADDR - ANGR_BASE
                    else:
                        pc = ret_val[0][-1].break_edges[-1][-1].addr + BASE_ADDR - ANGR_BASE # 此处是需要跳转到的位置
                else:
                    # 当前无限循环的部分先退出
                    print("NO BREAK EDGE")
                    break
                continue
            # 检查当前指令是否是rep stosd
            if Hooking_unsolvable_inst(self.ctx,instruction):
                # 如果hook到难跨越的指令就手动执行
                pc = pre_pc
                # pc = pc + 8

            # 检查本次是否是强制跳转用到jmp rax
            
            # 这里进行强制路径跳转
            # if switch_node is not None:
            #     for per_node in switch_node: # 从前向后遍历
            #         if str(instruction) in per_node:
            #             # 找到一个结点
            #             pc = per_node[str(instruction)] 
            #             # 已经到达的节点则从路径中移除
            #             del per_node[str(instruction)] 
            #             # 这里是一次只取出一个结点进行下一跳
            #             break
            if count_inst > MAX_INST_TIMES:
                print("Process Too Much Instructions!")
                break
            force_break_pc = self.lp_controller.control_loop_times(instruction, self.ctx, BASE_ADDR,pc)
            if force_break_pc is not None and force_break_pc is not True:
                pc = force_break_pc
            try:
                if self.switch_node is not None: # 这里经过了G1之后再继续控制跳转
                    print(int(list(self.switch_node[-1].keys())[0].split(':')[0], 16))
                    if int(list(self.switch_node[-1].keys())[0].split(':')[0], 16) == instruction.getAddress():
                        pc = list(self.switch_node[-1].values())[0]
                        # print(self.ctx.getTaintedMemory())
                        self.switch_node.pop()
                        if len(self.switch_node) == 0:
                            self.switch_node = None
            except:
                pass
            # if pc ==  0x8048b90:
            #     # 强制跳转不执行
            #     self.ctx.setConcreteRegisterValue(self.ctx.registers.eax, 0)
                # pc = 0x8049BA1

    def exe_symbolic(self,
                     path_for_emu, # cmp指令
                     start_addr,
                     current_path, # jmp 指令位置
                     target_addr, # 执行结束位置
                     ):
        '''
            该函数的作用是对单条路径做符号执行
        '''
        if not start_addr:
            start_addr=self.initial_entry_point
        my_path=per_path_contatiner()
        # 这里记录的是cmp指令
        path_cmp = []
        # 这里记录cmp指令的下一个选择True / False
        new_c = []
        for node_dict in path_for_emu:
            path_cmp += [int(inst.split(':')[0],16) if type(inst) is str else inst.getAddress() for inst in list(node_dict.keys())]
            if type(list(node_dict.values())[-1]) is int:
                new_c.append(list(node_dict.values())[-1])
            else:
                new_c.append(1 if list(node_dict.values())[-1] is True else 0)
        # TODO(这里施加了一个转换，由于后面符号执行时使用的一个跳转可能出现多次，因此一个地址可能有多个跳转方向
        new_c=[[c] for c in new_c] # 这里将其转化为[[1]]的格式
        my_path.add_new_node(new_addr=path_cmp,
                             new_choice=new_c,
                             addr_to_inst=current_path) # 这里用于记录指令间的关系
        # 这里将最后一跳设置为目标状态
        my_path.add_target_addr(target_addr=target_addr)
        my_path.add_exit_point(exit_addr=target_addr)
        my_emu=path_emulator(
            thread_id=1,
            context=self.ctx,
            start_address=start_addr,
            path_model=my_path,
            lib_gst_code_seg = self.Target_Binary_Code,
            base_addr = BASE_ADDR
        )
        my_emu.add_cycle_mode(self.lp_controller) # 这里的cdg是cycle_mode
        my_emu.start()
        my_emu.join()
        res_dict=my_emu.get_result()
        return res_dict

    def emu_single_path(self,
                        current_jmp_path,
                        # 这个是记录地址：指令的结构
                        tainted_address,
                        gadget_address,
                        start_address=None,
                        current_cmp_path=None, # 该函数的作用是用于标注cmp指令，便于后续的符号执行部分
                        exit_address=None,
                        get_state_addr= None, # 该参数用于找到一个位置，当运行到该位置时，直接返回一个
                        mem_map = None, # 这里传入从外部解出的特定解
                        target_addr = None,
                        record_model_list = [], # 特殊的处理函数
                        is_search_gdt = True, # 这里用于检查是否进行gadget搜索
                        tainted_mem = None, # 这里设置需要进行污染的内存
                        start_taint_addr = None
                        ): # 该函数用于对单个路径进行搜索
        '''
            这里还是需要对目标路径运行求解
        '''
        symbol_mem_map = None
        # # 此处用于获取运行结果
        if mem_map is not None:
            symbol_mem_map=mem_map
        elif 'jmp' in str(list(current_jmp_path[-1].keys())[0]):
            symbol_mem_map = [] # 如果是jmp rax使用强制跳转，无需进行符号执行求解
        else:
            symbol_mem_map=self.exe_symbolic(path_for_emu=deepcopy(current_cmp_path),start_addr=start_address,current_path=deepcopy(current_jmp_path),target_addr=target_addr)
        # 这里获取的是对应的输入内容
        if symbol_mem_map is None:
            print("untouchable path!")
            return None, None
        
        # 这里只对原始的输入做了限制
        # 这里的symbol_mem_map存储的是相应的字典进行映射
        # 这里设置相应的内存，保证当前的路径是目标路径
        
        '''
            call 预先标记好如果是某个函数要做哪些事情
            如果是指针之间的赋值，那就是个解引用这一类的过程，该过程的取值应该没有办法直接使用符号执行求出
        '''
        self.fresh()
        self.instruct_queue.clear()
        if get_state_addr is None:
            for mem_addr in symbol_mem_map:
                self.ctx.setConcreteMemoryAreaValue(mem_addr, bytes(chr(symbol_mem_map[mem_addr]).encode()))
                self.ctx.taintMemory(MemoryAccess(mem_addr, CPUSIZE.BYTE)) # 这里要设置对应的污染数据
                self.ctx.symbolizeMemory(MemoryAccess(mem_addr,CPUSIZE.BYTE))
        
        pc=start_address if start_address is not None else self.initial_entry_point
        new_path_list_all=[]
        new_path_list_all_emu=[]
        pc_list={}
        
        pc_list_emu={}
        self.taint_record={} # 这里对记录清空
        last_instruct=None
        need_out = False
        loop =[]
        jmp_addr_list = []
        switch_addr_list = {} # 这里记录本次路径中Switch节点存在的位置
        for jmp_node in current_jmp_path:
            try:
                jmp_addr_list.append(list(jmp_node.keys())[0].getAddress())
            except:
                jmp_addr_list.append(int(list(jmp_node.keys())[0].split(':')[0], 16))
            if 'jmp' in str(list(jmp_node.keys())[0]):
                if int(str(list(jmp_node.keys())[0]).split(':')[0], 16) in switch_addr_list:
                    switch_addr_list[int(str(list(jmp_node.keys())[0]).split(':')[0], 16)].append(list(jmp_node.values())[0])
                else:
                    switch_addr_list[int(str(list(jmp_node.keys())[0]).split(':')[0], 16)] = [list(jmp_node.values())[0]]
        # 记录本次执行新发现的gdt
        new_gdt_list = []
        self.last_taint_state = get_taint_state(self.ctx)
        while pc:
            if not (pc < self.Target_Binary_Code['start'] + self.Target_Binary_Code['size'] and pc >self.Target_Binary_Code['start']):
                print("jump_out_of_range")
                # 如果这里是call出去的，那么说明还能回来
                if 'call' in str(self.instruct_queue[-1]):
                    # 那就直接pop栈然后返回
                    pc = self.pop_stack()
                else:   
                    break
            # Fetch opcode
            new_gadget = None
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16) # 这里是取出其中的操作码
            '''
                这里直接传入本次要去的地址
            '''
            ret_val,loop_flag = self.handle_loop(pc, BASE_ADDR) 
            if loop_flag == -1:
                if len(ret_val[0][-1].break_edges) != 0:
                    if len(ret_val[0][-1].break_edges) > 1:
                        # 这里采用随机探索的方式选择一个break_edge、
                        pc = ret_val[0][-1].break_edges[-1][-1].addr + BASE_ADDR - ANGR_BASE
                        # pc = ret_val[0][-1].break_edges[random.randint(0, len(ret_val[0][-1].break_edges)-1)][-1].addr + BASE_ADDR - ANGR_BASE
                    else:
                        pc = ret_val[0][-1].break_edges[-1][-1].addr + BASE_ADDR - ANGR_BASE # 此处是需要跳转到的位置
                else:
                    # 当前无限循环的部分先退出
                    print("NO BREAK EDGE")
                    break
                continue
            '''
                如果当前位置不对直接continue
            '''
            instruction = Instruction(pc, opcode)
            self.ctx.processing(instruction) # 执行指令
            pre_pc = instruction.getNextAddress() # 
           
            mode_generate_path = None
            mode_generate_path_cmp = None
            # 这里到达预定位置后设置污染内容
            if tainted_mem is not None:
                if pc == start_taint_addr:
                    base_addr = tainted_mem[0]
                    max_addr = tainted_mem[-1]
                    tmp_base = base_addr
                    while tmp_base < max_addr:
                        self.ctx.taintMemory(MemoryAccess(tmp_base,CPUSIZE.DQQWORD))
                        self.ctx.symbolizeMemory(MemoryAccess(tmp_base,CPUSIZE.BYTE))
                        tmp_base += CPUSIZE.DQQWORD
                    tainted_mem = None # 防止进行二次污染，这里直接设置为None

            loop = ret_val # 这里暂时不需要做判断，因为当前的状态
            if DEBUG is True:
                if instruction.isTainted():
                    RESULT_log(instruction,DEBUG)
                else:
                    DEBUG_log(instruction,DEBUG)

            '''
                预先标记受污染指令
            '''
            if pc in tainted_address: # 如果当前的指令是
                if str(instruction).split(":")[-1].split()[0] == 'call':
                    self.last_call_taint=True # 这里表明有可能是进行库函数调用
                else:
                    target_tainted,taint_type=get_target_oprand(instruction)
                    if taint_type == 1: # 这个位置开始进行内存的污染
                        self.ctx.taintMemory(target_tainted)
                    elif taint_type == 0 : # 这个位置开始进行寄存器的污染
                        self.ctx.taintRegister(target_tainted)
                        self.ctx.symbolizeRegister(target_tainted) # 对寄存器进行符号化的操作
                    # 这里注意就不再考虑标注错误的情况

            # Process
            if 'ret' in str(instruction) or 'leave' in str(instruction):
                self.last_call_taint=False
            # 如果执行到停止指令或者预设的退出地址就结束
            if instruction.getType() == OPCODE.X86.HLT or pc == exit_address or self.check_repeat_instruct():
                break

            # Simulate routines
            self.ctx,is_new_libc_gadget,hooking_flag=self.hookingHandler(self.ctx,self.last_call_taint,symbol_mem_map,loop,mode_generate_path_cmp,mode_generate_path)
            if is_search_gdt and mem_map is None:
                new_gadget = self.handle_instruct(instruction,mode_generate_path_cmp,mode_generate_path,loop)
            for solve_model in record_model_list:
                if is_new_libc_gadget is not None and (new_gadget is None or new_gadget is False):
                    new_gadget = is_new_libc_gadget # 这里修改一下，传入的是指令序列
                ret=solve_model.solve(instruction,self.ctx,hooking_flag, new_gadget) # 将所有的操作都打包到一个函数中
                try:
                    # 此处开始进行
                    mode_generate_path, mode_generate_path_cmp = solve_model.get_main_path()
                except:
                    pass
                if ret == 1: # 如果当前的处理函数的返回结果是1，则证明目前条件已经足以让程序退出
                    return
                elif type(ret) == dict and new_gadget is not None and new_gadget is not False: # 如果这里返回的是一个字典，则表明当前再获得的gdt需要载入range属性
                    self.gdt_mode_list[-1].taint_range = ret # 这里向最新加入的gdt装载相应指令的污染情况
            if new_gadget is not None and new_gadget is not False:
                new_gdt_list.append(new_gadget) # 这里缓存以下新的gdt
            # 如果当前对应的gadget既不是None也不是False，那说明是真的产生了一个gadget
            if new_gadget is not None and new_gadget is not False:
                # 这里肯定是取出最后一个gadget添加路径
                self.gadget_path[-1] = mode_generate_path_cmp
                self.gadget_path_jmp[-1] = mode_generate_path
                self.gdt_mode_list[-1].g_jmp_path = mode_generate_path
                self.gdt_mode_list[-1].path_to_gadget = mode_generate_path_cmp

            '''
                静态搜索gadget部分
            '''

            if pc == get_state_addr: # 检查当前的状态是否是想要到达的状态，如果是则直接返回
                print("approached gadget!")
                return self.ctx, instruction.getNextAddress()

            if ANALYSE_MODE is X86_32:
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
            else:
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
            last_loop_flag=loop_flag
            self.last_taint_state = get_taint_state(self.ctx)
            self.push_queue_ram(instruction) # 这里对指令进行缓存
            '''
                针对jmp rax实现强制跳转
            '''

            try:
                pc_list = switch_addr_list[ instruction.getAddress()]
                pc = pc_list[0]
                del pc_list[0]
            except:
                pass
            if Hooking_unsolvable_inst(self.ctx,instruction):
                # 如果hook到难跨越的指令就手动执行
                pc = pre_pc

        return new_path_list_all,new_path_list_all_emu
    
    def sort_again(self, jmp_path_list, cmp_path_list):
        # 使用 zip 将两个列表的对应元素组合成元组，然后进行排序
        sorted_tuples = sorted(zip(jmp_path_list, cmp_path_list), key=lambda x: len(x[0]))

        # 使用 zip 和列表解析将排序后的元组拆分回两个列表
        sorted_jmp_path_list, sorted_cmp_path_list = zip(*sorted_tuples)

        return list(sorted_jmp_path_list), list(sorted_cmp_path_list)

    # 该函数用于对路径进行排序
    def sort_path(self, jmp_path_list, cmp_path_list):
        head_jmp_path = []
        head_cmp_path = []
        tail_j_path = []
        tail_c_path = []
        # 将末尾是jmp rax的路径优先处理
        combined_list = list(zip(jmp_path_list, cmp_path_list))
        random.shuffle(combined_list)
        jmp_path_list, cmp_path_list= zip(*combined_list)
        cmp_path_list = list(cmp_path_list)
        jmp_path_list = list(jmp_path_list)
        for j_path, c_path in zip(jmp_path_list,cmp_path_list):
            # 这里取出最后一个节点
            if 'jmp' in list(j_path[-1].keys())[0]:
                tail_j_path.append(j_path)
                tail_c_path.append(c_path)
            else:
                head_cmp_path.append(c_path)
                head_jmp_path.append(j_path)
        
        return self.sort_again(head_jmp_path+tail_j_path, head_cmp_path+tail_c_path)

def check_sub_set(main_path_list, new_path):
    '''
    new_path的结构 [{address1:True_or_False},{address2:True_or_False}]
    main_path_list的结构 [
        [{address1:True_or_False},{address2:True_or_False}],
        [{address1:True_or_False},{address2:True_or_False}],
    ]
    '''
    for main_path in main_path_list:
        # 检查new_path是否在main_path_list中
        if type(main_path) is not list:
            main_path = [main_path]
        if new_path == main_path:
            return False
        # 检查new_path是否是main_path的前缀
        if len(new_path) <= len(main_path):
            is_prefix = True
            for i, new_address in enumerate(new_path):
                if new_address != main_path[i]:
                    is_prefix = False
                    break
            if is_prefix:
                return False
    return True


# 该类继承了TaintAnalyser
class fast_emuer(Thread, TaintAnalyser):
    def __init__(self,new_ctx,new_entry_point, new_base_addr, thread_id, 
                 current_branch=None,switch_node = None ):
        # final_node 用于记录jmp rax的跳转结果
        # self.dataflow_controller=Data_flow_controler(new_ctx, new_entry_point,mem_cache=memoryCache,
                                                    # code_cache = codeCache,tainted_mem=TAINTED_MEM)
        self.lp_controller = loop_controller(sys.argv[1],cfg_model =CFG_MODEL, loop_list = LOOP_LIST,angr_proj = ANGR_PROJ)
        super().__init__() # Thread父类init
        super(Thread,self).__init__(
            ctx=new_ctx, # 当前的上下文状态
            entry_point=new_entry_point, #
            CodeCache = codeCache,   
            lp_controller= self.lp_controller,
            # dataflow_controller=self.dataflow_controller
        ) # TaintAnalyser init
        self.thread_id =  thread_id
        self.new_base_addr = new_base_addr
        # 记录jmp rax的结果, str(jmp rax) : next_choice_addr
        self.current_branch = current_branch # 在一次运行结束后该路径中的结点全部弹出结束
        self.switch_node = switch_node 
        '''
            ↑ 这里的部分要对jmp rax进行处理
        '''
    
    # 重写多线程函数
    def run(self):
        # 创建当前多线程函数
        self.myPath_solver = path_solver(sys.argv[1],BASE_ADDR,ANGR_PROJ,cfg_model=CFG_MODEL,loop_list =LOOP_LIST) # 这里只需要传入相应的cfg图和程序加载的基地址即可
        # 这里创建了一个新的对象，没有用到全局变量，应该不会产生相互的影响
        self.first_run(record_model_list=[
            # self.dataflow_controller,
        self.myPath_solver],new_path_map = self.current_branch,slow_run=False
                       ,switch_node = self.switch_node)

    def get_gadget(self):
        return self.gdt_mode_list

def load_all_static(bin_name):
    '''
        该函数根据程序名称加载相应的中间文件
    '''
    angr_loader = multi_loader("./MidResult/"+bin_name+"/"+bin_name+'.angr_proj')
    cfg_loader = multi_loader("./MidResult/"+bin_name+"/"+bin_name+'.cfg_model')
    lp_loader = multi_loader("./MidResult/"+bin_name+"/"+bin_name+'.looplist')
    print("./MidResult/"+bin_name+"/"+bin_name+'.looplist')
    bmap_loader = multi_loader("./MidResult/"+bin_name+"/"+bin_name+'.BRANCH_MAP')
    #  开启所有线程
    angr_loader.start()
    cfg_loader.start()
    lp_loader.start()
    bmap_loader.start()
    # 等待所有线程
    angr_loader.join()
    cfg_loader.join()
    lp_loader.join()
    bmap_loader.join()

    # 返回结果
    return angr_loader.get_res(), cfg_loader.get_res(), lp_loader.get_res(),  bmap_loader.get_res()

def show_time(start_time):
    end_time = time()
    run_time = end_time - start_time    
    # 将运行时间转换为时分秒格式
    hours = int(run_time // 3600)
    minutes = int((run_time % 3600) // 60)
    seconds = int(run_time % 60)

    # 打印运行时间
    print(f"Finished in  {hours}h {minutes}m {seconds}s")


def main():
    '''
        初始化启动程序 ,sys.argv[0] 其实是程序文件本身
        sys.argv[3] : cfg_model
        sys.argv[4] : looplist
    '''
    if len(sys.argv) < 2:
        ERROR_log("Too few args",True)
        sys.exit(1)

    print("[!] Make Sure You've Finished the Static Analysis")
    '''
        加载 angr_loader.get_res(), cfg_loader.get_res(), lp_loader.get_res(),  bmap_loader.get_res()
    '''
    # 记录开始时间
    start_time = time()
    global BRANCH_MAP
    global ANGR_PROJ
    global CFG_MODEL
    global LOOP_LIST
    ANGR_PROJ, CFG_MODEL,LOOP_LIST,BRANCH_MAP = load_all_static(sys.argv[1].split('/')[-1])
    for per_loop in LOOP_LIST:
        if len(per_loop.break_edges) == 0:
            LOOP_LIST.remove(per_loop)
    global NOW_ARCH
    global customRelocation
    # 创建一个文件夹来存储实验数据
    
    if is64Arch(sys.argv[1]):
        NOW_ARCH = ARCH.X86_64
        customRelocation = customRelocation64
    else:
        NOW_ARCH = ARCH.X86
        customRelocation = customRelocation32
    
    # 设置二者的对应关系
    ctx = TritonContext(NOW_ARCH)
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    ctx,entry_point,args,code_base_adr ,real_base=initialize()
    global GadgetFunc2Addr
    for per_line in customRelocation:
        if per_line[0] in Target_Gadget:
            GadgetFunc2Addr[per_line[0]] = per_line[-1]
    # 这里获取全局地址
    global BASE_ADDR 
    # 这里对全局变量的基地址进行赋值操作
    BASE_ADDR = code_base_adr


    lpcontroller=loop_controller(file_path = sys.argv[1],cfg_model =CFG_MODEL, loop_list = LOOP_LIST,angr_proj = ANGR_PROJ)
    # Let's emulate the binary from the entry point
    # dataflow_controller = Data_flow_controler(ctx, entry_point,mem_cache=memoryCache,code_cache = codeCache,tainted_mem=TAINTED_MEM) # 这里默认从文件入口开始进行分析
    my_analyser=TaintAnalyser(ctx=ctx,
                              entry_point=entry_point,
                              lp_controller=lpcontroller,
                              tainted_mem=TAINTED_MEM, #
                              CodeCache = codeCache,
                            #   dataflow_controller = dataflow_controller
                              )
    
    myPath_solver = path_solver(sys.argv[1],BASE_ADDR,ANGR_PROJ,cfg_model=CFG_MODEL,loop_list =LOOP_LIST) # 这里只需要传入相应的cfg图和程序加载的基地址即可
    '''
        开始进行首次污点分析
    '''
   
    # 该对象用于实现对每个指令进行存储
    my_analyser.first_run(record_model_list=[
                                            # dataflow_controller,
                                            myPath_solver],angr_cfg=CFG_MODEL) # 首次路径探索
    '''
        首次污点分析生成新的路径进行探索
    '''
    global emuer_pool
    global searched_branched
    # TODO 这里要改一下，在探索时，要把所有线程中获取的路径进行汇总探索
    
    emuer_pool = sort_by_rank(emuer_pool)
    print("Got New Execuatable path", len(emuer_pool))
    thread_counter = 0
    new_thread_pool = []    
    final_gadget_list = []
    '''
        这里主线程先锁定，等待所有线程都启动后再进行查找
    '''
    while True:
        while True:
            with counter_lock:
                try:
                    first_item = next(iter(emuer_pool))
                except:
                    print("DEBUG: No More Iteration",len(emuer_pool))
                    show_time(start_time)
                    for per_thread  in new_thread_pool:
                        # 这里防止有没有完成的线程
                        per_thread.join()
                        final_gadget_list += per_thread.get_gadget()
                    return 
                # if list(emuer_pool[first_item].switch_node[-1].values())[-1] == 140737054775393:
                #     print("Got! TargetBraches")
                emuer_pool[first_item].start()
                new_thread_pool.append(emuer_pool[first_item])
                del emuer_pool[first_item]
                thread_counter += 1
                if thread_counter %4 == 0:
                    break
        for per_thread  in new_thread_pool:
            per_thread.join()
            final_gadget_list += per_thread.get_gadget()
        # 每开启两个线程的时候等一次
        with counter_lock:
            if len(emuer_pool) == 0: 
                    show_time(start_time)
                    print("[Debug] Run Out ALL Paths :",thread_counter)
                    return 
            emuer_pool = sort_by_rank(emuer_pool)
            '''
                这一部分后面要删掉
            '''
            # small_range = len(emuer_pool)
            # for per_pthd in range(small_range):
            #     if list(emuer_pool[per_pthd].switch_node[-1].values())[-1] != 140737054775393:
            #         del emuer_pool[per_pthd]
            # 遍历字典中的每个键值对，并删除不符合要求的元素
            # emuer_pool = {key: value for key, value in emuer_pool.items() if list(value.switch_node[-1].values())[-1] == 140737054775393}
        if (list(emuer_pool.keys())[0][-1] == 0 and not FORCERUN ) or (thread_counter > 12 and list(emuer_pool.keys())[0][-1] < 0.1 ) or thread_counter > 16 :
            show_time(start_time)
            # 如果不存在有价值的路径时就直接退出
            print("[Debug] Finish All Searching :",thread_counter)
            return 

# 去除路径一样的原语
def Filt_Primitives():
    print("Filtering ALL Primitives...")
    hash_table = [] #  该列表用于存储每一条路径的哈希值
    json_files = [file for file in os.listdir(sys.argv[1].split('/')[-1] + "_P1")]
    for file in json_files:
        file_path = os.path.join(sys.argv[1].split('/')[-1] + "_P1", file)
        with open(file_path, 'r') as json_file:
            data = json.load(json_file)
            # 在这里对加载的 JSON 数据进行处理
            tmp_hash = hash(tuple(data[0]["serial"])) 
            if tmp_hash in hash_table:
                os.remove(file_path)
            else:
                hash_table.append(tmp_hash)
    # 输出最终保留的原语数量
    print("Finish Filtering ALL! Got Primitives:", len(hash_table))
    # 获取文件夹中的所有文件
    import shutil
    folder_path = sys.argv[1].split('/')[-1] + "_P1"
    files = os.listdir(folder_path)

    # 根据文件长度进行排序
    files.sort(key=lambda x: os.path.getsize(os.path.join(folder_path, x)))

    # 遍历文件并重命名
    for i, file_name in enumerate(files):
        file_path = os.path.join(folder_path, file_name)
        new_file_name = sys.argv[1].split('/')[-1]+'.gdt'+str(i + 1) + '.json'  # 生成新的文件名
        new_file_path = os.path.join(folder_path, new_file_name)

        # 重命名文件
        shutil.move(file_path, new_file_path)

        print(f'Renamed "{file_name}" to "{new_file_name}"')
def add_count():
    from collections import Counter
    json_files = [file for file in os.listdir(sys.argv[1].split('/')[-1] + "_P1")]
    for file in json_files:
        file_path = os.path.join(sys.argv[1].split('/')[-1] + "_P1", file)
        with open(file_path, 'r') as json_file:
            data = json.load(json_file)
        # 计算"src_location"和"dst_location"的最大出现次数
        print(file_path)
        for item in data:
            src_location = item.get("src_location", [])
            dst_location = item.get("dst_location", [])
            target_location = item.get("target_adr", [])
            src_data_location = item.get("src_data_location",[])
            len_location = item.get("len_location",[])
            serial_ = item.get("serial", [])
            item["src_count"] = serial_.count(src_location)
            item["dst_count"] = serial_.count(dst_location)
            item['target_count'] = serial_.count(target_location)
            item['src_data_count'] = serial_.count(src_data_location)
            item['len_count'] = serial_.count(len_location)
        with open(file_path, 'w') as file:
            json.dump(data, file, indent=4)

if __name__ == '__main__':
    start_time = time()
    main()
    # # # 下面开始对原语进行筛选排序
    Filt_Primitives()
    show_time(start_time)
    add_count()
    
