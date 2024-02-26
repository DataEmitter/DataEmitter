from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,AST_REPRESENTATION,CALLBACK
from capstone import Cs, CS_ARCH_X86, CS_MODE_64
from threading import Thread
import dill
import time
from config.__config import *
import re
def extract_parts(expression):
    parts = re.split(r'[\+\-\*]', expression)
    parts = [part.strip() for part in parts if part.strip()]
    base_reg = parts[0] if len(parts) > 0 else None
    idx_reg = parts[1] if len(parts) > 1 else None
    imm1 = parts[2] if len(parts) > 2 else None
    imm2 = parts[3] if len(parts) > 3 else None
    if expression.count('+') + expression.count('-') == 2:
        # 这里说明是三个数运算,三个数要处理第二个数系数为1的情况
        pass
    elif expression.count('+') + expression.count('-') ==1 : # 两个数运算
        # 处理rax + rdx的情况
        if imm1 is None and idx_reg is not None:
            imm1 = '1'
        # 处理 rax + 1的问题
        try:
            int(idx_reg)
            imm2 = imm1
            idx_reg = None
            imm1 = None
        except:
            pass
    else:
        # 一个数只有base
        pass
    if expression.count('-') != 0:
        imm2 = '-'+imm2
    return base_reg, idx_reg, imm1, imm2

def twos_complement_to_int(hexadecimal, bits=64):
    # 将十六进制补码转换为有符号整数
    binary = bin(int(hexadecimal, 16))[2:].zfill(bits)
    decimal = int(binary, 2)
    if binary[0] == '1':  # 如果最高位是1，表示负数
        decimal = decimal - (1 << bits)
    return decimal

# 模拟某些没有进行任何处理的函数
'''
    如果当前函数的返回值为True则证明是triton无法处理的指令
'''
def Hooking_unsolvable_inst(ctx, inst):
    '''
        检查是否是rep stosd,将eax的内容向目标地址复制ecx次
    '''

    memsolve_inst_list = [
        'stosb',
        'stosw',
        'stosd'
        'stosq',
        # 上面仅仅是写入内容的size大小不同，其余相同。向edi指向的内容写eax * ecx
        'lodsb',
        'lodsw',
        'lodsd',
        'lodsq',
        # 该指令的作用是将esi指向的内存读入到eax寄存器中，并且该指令并不能增加rep等前缀，这是错误的
    ]
    # 该指令的本质就是进行内存的复制写入，其本身也是一种可以利用的gadget
    if 'rep stosd' in str(inst):
        mov_cod = inst.getPrefix()
        disa = inst.getDisassembly()
        Destnation = ctx.getConcreteRegisterValue(ctx.registers.edi)
        # 获取当前应该复制的次数
        RepeatTime = ctx.getConcreteRegisterValue(ctx.registers.ecx)
        #  获取当前的eax寄存器的内容
        WriteContent = ctx.getConcreteRegisterValue(ctx.registers.eax)
        #  设置当前程序中需要写入的内容
        # WritableContent = Num2WritableByte(WriteContent, 4) *RepeatTime
        # 向目标程序中循环写入内容
        for idx in range(RepeatTime):
            ctx.setConcreteMemoryValue(MemoryAccess(Destnation+idx*4, CPUSIZE.DWORD), WriteContent)
            if ctx.isRegisterTainted(ctx.registers.eax):
                ctx.taintMemory(MemoryAccess(Destnation+idx*4, CPUSIZE.DWORD))
        return True
    elif 'out' in str(inst) or 'vcvtsi2sd' in str(inst) or 'vdivsd' in str(inst):
        '''
            这里的对out指令进行建模
        '''
        return True
    elif inst.getAddress() in [0x41CE10,0x41CFAC]:
        return True

    return False

'''
    本文件用于存储在污点分析中使用的各类
'''
def show_time(start_time):
    end_time = time.time()
    run_time = end_time - start_time    
    # 将运行时间转换为时分秒格式
    hours = int(run_time // 3600)
    minutes = int((run_time % 3600) // 60)
    seconds = int(run_time % 60)

    # 打印运行时间
    print(f"Finished in  {hours}h {minutes}m {seconds}s")
class multi_loader(Thread):
    def __init__(self,file_name):
        super().__init__() # Thread父类init
        # 该变量用于记录当前的分析结果
        self.result = None
        self.file_name = file_name

    def run(self):
        print("[*] Loading",self.file_name)
        with open(self.file_name, 'rb') as f:
            self.result = dill.load(f)
        print("[*]",self.file_name,"Finish Loading")
    # 获取多线程的分析结果
    def get_res(self):
        return self.result
# 该函数用于获取下一条指令的操作码
def get_next_inst_oprand(inst,
                         opcode, # 注意这里的opcode是传入
                         ):
    next_pc = inst.getNextAddress()
    next_instruction = Instruction(next_pc,opcode)
    cs = Cs(CS_ARCH_X86, CS_MODE_64)
    next_instructions = list(cs.disasm(next_instruction.getOpcode(), next_pc))
    # 遍历并打印每条指令
    for insn in next_instructions:
        if next_pc == insn.address:
            return insn.mnemonic
        
    raise Exception("No next Addr")
    
ANGR_BASE = 0x400000
# 该函数用于检查当前程序架构
def is64Arch(file_path):
    with open(file_path, "rb") as f:
        return f.read(5)[-1] == 2
# 该函数用于保存前一时刻的寄存器的污染状态
def get_taint_state(ctx):
    taint_lib = {}
    try:
        taint_lib['rax'] = ctx.isRegisterTainted(ctx.registers.rax)
        taint_lib['rbx'] = ctx.isRegisterTainted(ctx.registers.rbx)
        taint_lib['rcx'] = ctx.isRegisterTainted(ctx.registers.rcx)
        taint_lib['rdx'] = ctx.isRegisterTainted(ctx.registers.rdx)
        taint_lib['rsi'] = ctx.isRegisterTainted(ctx.registers.rsi)
        taint_lib['rdi'] = ctx.isRegisterTainted(ctx.registers.rdi)
        taint_lib['rbp'] = ctx.isRegisterTainted(ctx.registers.rbp)
        taint_lib['rsp'] = ctx.isRegisterTainted(ctx.registers.rsp)
        taint_lib['rip'] = ctx.isRegisterTainted(ctx.registers.rip)
        taint_lib['rsp'] = ctx.isRegisterTainted(ctx.registers.rsp)
        taint_lib['r8'] = ctx.isRegisterTainted(ctx.registers.r8)
        taint_lib['r9'] = ctx.isRegisterTainted(ctx.registers.r9)
        taint_lib['r10'] = ctx.isRegisterTainted(ctx.registers.r10)
        taint_lib['r11'] = ctx.isRegisterTainted(ctx.registers.r11)
        taint_lib['r12'] = ctx.isRegisterTainted(ctx.registers.r12)
        taint_lib['r13'] = ctx.isRegisterTainted(ctx.registers.r13)
        taint_lib['r14'] = ctx.isRegisterTainted(ctx.registers.r14)
        taint_lib['r15'] = ctx.isRegisterTainted(ctx.registers.r15)
        taint_lib['fs'] = ctx.isRegisterTainted(ctx.registers.fs)
    except:
        taint_lib['eax'] = ctx.isRegisterTainted(ctx.registers.eax)
        taint_lib['ebx'] = ctx.isRegisterTainted(ctx.registers.ebx)
        taint_lib['ecx'] = ctx.isRegisterTainted(ctx.registers.ecx)
        taint_lib['edx'] = ctx.isRegisterTainted(ctx.registers.edx)
        taint_lib['esi'] = ctx.isRegisterTainted(ctx.registers.esi)
        taint_lib['edi'] = ctx.isRegisterTainted(ctx.registers.edi)
        taint_lib['ebp'] = ctx.isRegisterTainted(ctx.registers.ebp)
        taint_lib['esp'] = ctx.isRegisterTainted(ctx.registers.esp)
        taint_lib['eip'] = ctx.isRegisterTainted(ctx.registers.eip)
        taint_lib['esp'] = ctx.isRegisterTainted(ctx.registers.esp)

    return taint_lib


def showDebugInfo(ctx):
    try:
        print('rax:', hex(ctx.getConcreteRegisterValue(ctx.registers.rax)), ctx.isRegisterTainted(ctx.registers.rax))
        print('rbx:', hex(ctx.getConcreteRegisterValue(ctx.registers.rbx)), ctx.isRegisterTainted(ctx.registers.rbx))
        print('rcx:', hex(ctx.getConcreteRegisterValue(ctx.registers.rcx)), ctx.isRegisterTainted(ctx.registers.rcx))
        print('rdx:', hex(ctx.getConcreteRegisterValue(ctx.registers.rdx)), ctx.isRegisterTainted(ctx.registers.rdx))
        print('rsi:', hex(ctx.getConcreteRegisterValue(ctx.registers.rsi)), ctx.isRegisterTainted(ctx.registers.rsi))
        print('rdi:', hex(ctx.getConcreteRegisterValue(ctx.registers.rdi)), ctx.isRegisterTainted(ctx.registers.rdi))
        print('rbp:', hex(ctx.getConcreteRegisterValue(ctx.registers.rbp)), ctx.isRegisterTainted(ctx.registers.rbp))
        print('rsp:', hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)), ctx.isRegisterTainted(ctx.registers.rsp))
        print('rip:', hex(ctx.getConcreteRegisterValue(ctx.registers.rip)), ctx.isRegisterTainted(ctx.registers.rip))
        print("-----------------------------------------------------------")
        print(ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp), 8).hex())
        hex(ctx.getConcreteRegisterValue(ctx.registers.rsp))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)), '-->', ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp), 8).hex(), ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.rsp)))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)+8),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp)+8, 8).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.rsp)+8))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)+16),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp)+16, 8).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.rsp)+16))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)+24),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp)+24, 8).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.rsp)+24))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.rsp)+32),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.rsp)+32, 8).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.rsp)+32))
    except:
        print('eax:',hex(ctx.getConcreteRegisterValue(ctx.registers.eax)),ctx.isRegisterTainted(ctx.registers.eax))
        print('ebx:',hex(ctx.getConcreteRegisterValue(ctx.registers.ebx)),ctx.isRegisterTainted(ctx.registers.ebx))
        print('ecx:',hex(ctx.getConcreteRegisterValue(ctx.registers.ecx)),ctx.isRegisterTainted(ctx.registers.ecx))
        print('edx:',hex(ctx.getConcreteRegisterValue(ctx.registers.edx)),ctx.isRegisterTainted(ctx.registers.edx))
        print('esi:',hex(ctx.getConcreteRegisterValue(ctx.registers.esi)),ctx.isRegisterTainted(ctx.registers.esi))
        print('edi:',hex(ctx.getConcreteRegisterValue(ctx.registers.edi)),ctx.isRegisterTainted(ctx.registers.edi))
        print('ebp:',hex(ctx.getConcreteRegisterValue(ctx.registers.ebp)),ctx.isRegisterTainted(ctx.registers.ebp))
        print('esp:',hex(ctx.getConcreteRegisterValue(ctx.registers.esp)),ctx.isRegisterTainted(ctx.registers.esp))
        print('eip:',hex(ctx.getConcreteRegisterValue(ctx.registers.eip)),ctx.isRegisterTainted(ctx.registers.eip))
        print("-----------------------------------------------------------")
        print(ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp), 4).hex())
        hex(ctx.getConcreteRegisterValue(ctx.registers.esp))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.esp)), '-->', ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp), 4).hex(), ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.esp)+4),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp)+4, 4).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+4))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.esp)+8),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp)+8, 4).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+8))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.esp)+12),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp)+12, 4).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+12))
        print(hex(ctx.getConcreteRegisterValue(ctx.registers.esp)+16),'-->',ctx.getConcreteMemoryAreaValue(ctx.getConcreteRegisterValue(ctx.registers.esp)+16, 4).hex(),ctx.isMemoryTainted(ctx.getConcreteRegisterValue(ctx.registers.esp)+16))

# 进行内存字节的转换
def Num2WritableByte(number,TargetByte):
    '''
        TargetByte: 设置要转换的字节数，例如设置为4则是最终生成一个四字节的比特字符串
    '''
    import struct
    byte_data = struct.pack("<I", number)

    # 将字节串写入内存
    memory = bytearray(TargetByte)
    memory[:TargetByte] = byte_data

    # 打印内存中的字节序列
    return memory
def check_whether_in_gadget(t_gadget,gadget_list):
    '''
        检查当前找到的gadget是否在已经在gadget中，这里不能只按照一条指令
    '''
    for per_gadget in gadget_list:
        flag=1
        for per_ins,my_ins in zip(t_gadget,per_gadget):
            if str(per_ins.instruction) != str(my_ins.instruction):
                flag=0
                break # 如果比对过程中不相同就直接下一个
        if flag == 1:
            return True
    return False # 遍历完了还没有相同的就直接
# 该函数用于比较两个操作数是否相同,主要解决rax,eax,ah,al等是否相同的问题
def is_op_equal(target_op,my_op,normal=False):
    if type(target_op) != str:
        target_op=str(target_op).split(":")[0]
    if type(my_op) != str:
        my_op=str(my_op).split(":")[0]
    if normal:# 此处使用正常匹配
        if my_op == target_op:
            return True
        else:
            return False
    if len(re.findall(r'\d+', target_op)) != 0:
        if  re.findall(r'\d+', target_op) == re.findall(r'\d+', my_op):
            return True
    target_op=target_op.replace('e','').replace('r','').replace('h','').replace('l','').replace('x','')
    my_op=my_op.replace('e','').replace('r','').replace('h','').replace('l','').replace('x','')
    if target_op == my_op:
        return True
    else:
        return False

def check_op_in_list(target_list:list,target_op):
    for l_op in target_list:
        if is_op_equal(l_op,target_op):
            return True
    return False

# 获取跳转目标
def get_jump_target(ctx,instruction):
    return str(instruction.getOperands()[0]).split(":")[0]

def change_to_oppsite(x):
    '''
        该函数用于返回一个数的补码
    '''
    if type(x)==str:
        # 如果是字符串
        x=int(x,16)
    if len(bin(x)) < 66 or bin(x)[2]=='0': # 本身就是正数就不用管
        return x
    else:
        return -((~x&0xffffffff)+1) # 按位取反得到原码


# 该函数用于对列表进行去重合并操作
def conmbine_list(target_path,new_path,record_list):

    for p_path in new_path:
        if p_path not in record_list and p_path not in target_path: # 和记录路径中的内容进行比较
            target_path.append(p_path)
            record_list.append(p_path)
    return target_path,record_list

def loadBinary(ctx, path):
    import lief
    # Map the binary into the memory
    binary = lief.parse(path)
    phdrs  = binary.segments # 这里是取出的内存的地
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        # debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))

        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content)) # 这里是直接将二进制文件中的内容设置到了对应的位置,这里在整体调试的时候要删掉
    
    return binary



# 该类是一个虚拟机，用于对代码片段进行模拟执行
class vm_emulator():
    def __init__(self,
                 taint_analyser, # 直接传入一个污点分析器便于后续管理
                 code_base_adr,
                 c_context='amd64'
                 ) -> None:
        self.context=c_context # 设置当前的分析上下文,这里是指pwntools中的上下文关系,便于后续插入代码进行上下文分析
        self.taint_analyser = taint_analyser # 这里的污点分析器 
        self.code_base_adr = code_base_adr
    '''
        当前函数是为gadget做上下文分析,的确还是需要上下文关系
    '''

    def fresh(self):
        self.taint_analyser.fresh() # 直接使用他的fresh即可

    def emu_ign(self,
                start_addr, # 该位置用于记录所有已经找到的gadget1
                end_addr, # 结束位置
                watch_oprand = None, # 此处是要进行监视的各个部分
                record_model_list = [], # 该函数列表的作用是传入所有用于记录的对象
                ): # 
        self.start_addr = start_addr # 执行起始位置，这里传入的应该是一个具体地址
        self.end_addr = end_addr # 这里应该传入的是一个地址的集合
        self.watch_oprand = watch_oprand # 这里记录在运行过程中要监视的部分，这里不是register对象就是memory,所以直接看就行
        '''
            功能一：在已知代码内容的情况下，不需要上下文，直接对循环体执行观察寄存器前后变化即可
        '''
        # 从头开始执行到gadget所在loop
        self.taint_analyser.fresh() # 这里对上下文做一个刷新操作 
        ctx = self.taint_analyser.ctx # 这里取出对应的上下文
        
        if watch_oprand is not None: # 说明此时是用于进行gadget分析的情况，此时的
            pc = self.start_addr + self.code_base_adr - ANGR_BASE # 取出起始位置开始
            new_start = self.start_addr + self.code_base_adr - ANGR_BASE
            new_end = self.end_addr + self.code_base_adr - ANGR_BASE
        else:
            new_start = self.start_addr
            new_end = self.end_addr
            pc = self.start_addr
        data_bucket = {} # 这里用于缓存上次的数据
        for oprand in  self.watch_oprand:
            data_bucket[str(oprand)] = []
        # 
        counter=0 # 用于记录循环次数
        while pc:
            # 取出操作码
            opcode = ctx.getConcreteMemoryAreaValue(pc, 16)
            # 创建指令
            instruction = Instruction(pc, opcode)
            # pre_pc=self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
            # pre_pc+=int(len(opcode)/8) # 加上当前指令的长度就是下一条指令的长度  
            ctx.processing(instruction) # 执行指令
            print(instruction)
            # 不断取出其中的指令处理函数进行处理操作
            for solve_model in record_model_list:
                ret=solve_model.solve(instruction,ctx) # 将所有的操作都打包到一个函数中
                if ret == 1: # 如果当前的处理函数的返回结果是1，则证明目前条件已经足以让程序退出
                    return 
                
            if watch_oprand is not None: # 这里只有当进行gadget能力构建的时候才会进行此类操作
                if pc ==  new_start or pc == new_end: # 进入或者跳出循环的时候都记录一下当前的情况
                    # 这里进入两次
                    counter+=1
                    if counter > 3: # 至少执行三次后做数据比较
                        # 此处开始检查当前的问题
                        for data_key in data_bucket:
                            current_list = data_bucket[data_key] # 这里取出来的是当前变量的所有内容
                            # 当出现什么行为的时候可以认为是递增器？？那就是出现每个数据的递增情况时
                            if get_gap(current_list): # 如果当前的gap是固定的，也就是每次是递增的，那么就认为当前操作是gadget的增强器
                                return True
                            else:
                                return False # 这里表明当前并不是一个gadget增强器
                    else:
                        for oprand in self.watch_oprand:
                            data_bucket[str(oprand)].append(ctx.getConcreteRegisterValue(oprand)) # 这里进行多次记录
            if instruction.getType() == OPCODE.X86.HLT or pc == new_end:
                break
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
            self.taint_analyser.hookingHandler(ctx,None,None) # 这里保证正常执行即可

            # 检查当前数据列表里各个数据之间的差值
def get_gap(data_list):
    if len(data_list) < 3:
        # 如果当前列表的长度太小则不做任何操作
        return False
    gap_list = []
    # 这里检查临近两个值之间的差值，如果差值是
    for idx in range(2,len(data_list)): # 这里从2和1之间开始检查
        gap=data_list[idx]-data_list[idx-1] # 这里找到两个数据之间的gap
        if gap not in gap_list:
            gap_list.append(gap) # 这里收集所有的gap
    if len(gap_list) == 1:
        return True
    return False