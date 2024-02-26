from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND
from config.__config import *
if ANALYSE_MODE is X86_32:
    from utils.libc_func_mod32 import *
    customRelocation = customRelocation32
else:
    from utils.libc_func_mod64 import *
    customRelocation = customRelocation64

def loadBinary(ctx, path):
    import lief
    # Map the binary into the memory
    binary = lief.parse(path)
    phdrs  = binary.segments # 这里是取出的内存的地
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        # debug('Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size))
        ctx.setConcreteMemoryAreaValue(vaddr, list(phdr.content)) # 这里是直接将二进制文件中的内容设置到了对应的位置
    
    return binary
def makeRelocation(ctx, binary):
    # 此处为什么随便定是可以的？
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    relocations = [x for x in binary.pltgot_relocations]
    relocations.extend([x for x in binary.dynamic_relocations])
    # extend 目的是在列表后面追加n个值
    # Perform our own relocations
    for rel in relocations:
        symbolName = rel.symbol.name
        symbolRelo = rel.address # offset
        for crel in customRelocation:
            if symbolName == crel[0]:
                ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2]) # 填充got表，在运行的时候最终一定会跳转到got表指向的最终地址，因此直接将该地址与重定位地址保持一致即可
                break
    return
def hookingHandler(ctx): 
        if ANALYSE_MODE is X86_32:
            pc = ctx.getConcreteRegisterValue(ctx.registers.eip)
        else:
            pc = ctx.getConcreteRegisterValue(ctx.registers.rip)

        for rel in customRelocation:
            if rel[2] == pc: 
                tmp= rel[1](ctx,None,None) 
                try:
                    ret_value=tmp[0]
                    ctx=tmp[1]
                except:
                    ret_value=tmp
                    
                if NOW_ARCH is ARCH.X86:
                    ctx.setConcreteRegisterValue(ctx.registers.eax, ret_value)

                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp), CPUSIZE.DWORD))

                    ctx.setConcreteRegisterValue(ctx.registers.eip, ret_addr)

                    ctx.setConcreteRegisterValue(ctx.registers.esp, ctx.getConcreteRegisterValue(ctx.registers.esp)+CPUSIZE.DWORD)
                else:
                    ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)

                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))
                    ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)
                    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD)
                
        return ctx



'''
    该函数的作用是获取一个上下文
'''
def get_ctx_binary(file_path:str):
    ctx = TritonContext(ARCH.X86)
    ctx.setMode(MODE.ALIGNED_MEMORY, True)
    binary = loadBinary(ctx, file_path)
    makeRelocation(ctx, binary)
    ctx.setConcreteRegisterValue(ctx.registers.ebp, BASE_STACK)
    ctx.setConcreteRegisterValue(ctx.registers.esp, BASE_STACK)
    return ctx, binary