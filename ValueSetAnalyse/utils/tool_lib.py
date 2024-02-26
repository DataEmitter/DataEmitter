from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,AST_REPRESENTATION,CALLBACK
from capstone import Cs, CS_ARCH_X86, CS_MODE_64
from threading import Thread
import dill
import time
from config import *



def twos_complement_to_int(hexadecimal, bits=64):
    
    binary = bin(int(hexadecimal, 16))[2:].zfill(bits)
    decimal = int(binary, 2)
    if binary[0] == '1':  
        decimal = decimal - (1 << bits)
    return decimal



def Hooking_unsolvable_inst(ctx, inst):
    

    memsolve_inst_list = [
        'stosb',
        'stosw',
        'stosd'
        'stosq',
        
        'lodsb',
        'lodsw',
        'lodsd',
        'lodsq',
        
    ]
    
    if 'rep stosd' in str(inst):
        mov_cod = inst.getPrefix()
        disa = inst.getDisassembly()
        Destnation = ctx.getConcreteRegisterValue(ctx.registers.edi)
        
        RepeatTime = ctx.getConcreteRegisterValue(ctx.registers.ecx)
        
        WriteContent = ctx.getConcreteRegisterValue(ctx.registers.eax)
        
        
        
        for idx in range(RepeatTime):
            ctx.setConcreteMemoryValue(MemoryAccess(Destnation+idx*4, CPUSIZE.DWORD), WriteContent)
            if ctx.isRegisterTainted(ctx.registers.eax):
                ctx.taintMemory(MemoryAccess(Destnation+idx*4, CPUSIZE.DWORD))
        return True
    elif 'out' in str(inst) or 'vcvtsi2sd' in str(inst) or 'vdivsd' in str(inst):
        
        return True

    return False


def show_time(start_time):
    end_time = time.time()
    run_time = end_time - start_time    
    
    hours = int(run_time // 3600)
    minutes = int((run_time % 3600) // 60)
    seconds = int(run_time % 60)

    
    print(f"Finished in  {hours}h {minutes}m {seconds}s")
class multi_loader(Thread):
    def __init__(self,file_name):
        super().__init__() 
        
        self.result = None
        self.file_name = file_name

    def run(self):
        print("[*] Loading",self.file_name)
        with open(self.file_name, 'rb') as f:
            self.result = dill.load(f)
        print("[*]",self.file_name,"Finish Loading")
    
    def get_res(self):
        return self.result

def get_next_inst_oprand(inst,
                         opcode, 
                         ):
    next_pc = inst.getNextAddress()
    next_instruction = Instruction(next_pc,opcode)
    cs = Cs(CS_ARCH_X86, CS_MODE_64)
    next_instructions = list(cs.disasm(next_instruction.getOpcode(), next_pc))
    
    for insn in next_instructions:
        if next_pc == insn.address:
            return insn.mnemonic
        
    raise Exception("No next Addr")
    
ANGR_BASE = 0x400000

def is64Arch(file_path):
    with open(file_path, "rb") as f:
        return f.read(5)[-1] == 2

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


def Num2WritableByte(number,TargetByte):
    
    import struct
    byte_data = struct.pack("<I", number)

    
    memory = bytearray(TargetByte)
    memory[:TargetByte] = byte_data

    
    return memory
def check_whether_in_gadget(t_gadget,gadget_list):
    
    for per_gadget in gadget_list:
        flag=1
        for per_ins,my_ins in zip(t_gadget,per_gadget):
            if str(per_ins.instruction) != str(my_ins.instruction):
                flag=0
                break 
        if flag == 1:
            return True
    return False 

def is_op_equal(target_op,my_op,normal=False):
    if type(target_op) != str:
        target_op=str(target_op).split(":")[0]
    if type(my_op) != str:
        my_op=str(my_op).split(":")[0]
    if normal:
        if my_op == target_op:
            return True
        else:
            return False
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


def get_jump_target(ctx,instruction):
    return str(instruction.getOperands()[0]).split(":")[0]

def change_to_oppsite(x):
    
    if type(x)==str:
        
        x=int(x,16)
    if len(bin(x)) < 66 or bin(x)[2]=='0': 
        return x
    else:
        return -((~x&0xffffffff)+1) 



def conmbine_list(target_path,new_path,record_list):

    for p_path in new_path:
        if p_path not in record_list and p_path not in target_path: 
            target_path.append(p_path)
            record_list.append(p_path)
    return target_path,record_list

def loadBinary(ctx, path):
    import lief
    
    binary = lief.parse(path)
    phdrs  = binary.segments 
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        

        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content)) 
    
    return binary




class vm_emulator():
    def __init__(self,
                 taint_analyser, 
                 code_base_adr,
                 c_context='amd64'
                 ) -> None:
        self.context=c_context 
        self.taint_analyser = taint_analyser 
        self.code_base_adr = code_base_adr
    

    def fresh(self):
        self.taint_analyser.fresh() 

    def emu_ign(self,
                start_addr, 
                end_addr, 
                watch_oprand = None, 
                record_model_list = [], 
                ): 
        self.start_addr = start_addr 
        self.end_addr = end_addr 
        self.watch_oprand = watch_oprand 
        
        
        self.taint_analyser.fresh() 
        ctx = self.taint_analyser.ctx 
        
        if watch_oprand is not None: 
            pc = self.start_addr + self.code_base_adr - ANGR_BASE 
            new_start = self.start_addr + self.code_base_adr - ANGR_BASE
            new_end = self.end_addr + self.code_base_adr - ANGR_BASE
        else:
            new_start = self.start_addr
            new_end = self.end_addr
            pc = self.start_addr
        data_bucket = {} 
        for oprand in  self.watch_oprand:
            data_bucket[str(oprand)] = []
        
        counter=0 
        while pc:
            
            opcode = ctx.getConcreteMemoryAreaValue(pc, 16)
            
            instruction = Instruction(pc, opcode)
            
            
            ctx.processing(instruction) 
            print(instruction)
            
            for solve_model in record_model_list:
                ret=solve_model.solve(instruction,ctx) 
                if ret == 1: 
                    return 
                
            if watch_oprand is not None: 
                if pc ==  new_start or pc == new_end: 
                    
                    counter+=1
                    if counter > 3: 
                        
                        for data_key in data_bucket:
                            current_list = data_bucket[data_key] 
                            
                            if get_gap(current_list): 
                                return True
                            else:
                                return False 
                    else:
                        for oprand in self.watch_oprand:
                            data_bucket[str(oprand)].append(ctx.getConcreteRegisterValue(oprand)) 
            if instruction.getType() == OPCODE.X86.HLT or pc == new_end:
                break
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)
            self.taint_analyser.hookingHandler(ctx,None,None) 

            
def get_gap(data_list):
    if len(data_list) < 3:
        
        return False
    gap_list = []
    
    for idx in range(2,len(data_list)): 
        gap=data_list[idx]-data_list[idx-1] 
        if gap not in gap_list:
            gap_list.append(gap) 
    if len(gap_list) == 1:
        return True
    return False