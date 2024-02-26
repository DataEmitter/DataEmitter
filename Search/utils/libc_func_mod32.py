'''
    本文件用于32位程序中对函数进行建模操作
    32位程序cdecl的堆栈平衡由调用者进行保证
'''
from copy import copy,deepcopy
import sys
import string
import re
import random
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND
from config.__config import *
from utils.tool_lib import Num2WritableByte
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9ffffff0


mallocCurrentAllocation = 0
mallocMaxAllocation     = 2048
mallocBase              = BASE_ALLOC
mallocChunkSize         = 0x0003000f
def reverse_path_constrain(path_list): # 这里是对列表中的所有路径条件进行取反操作
    for single_path in path_list:
        '''
            这里取出的结构是每一条路径的最后一跳结点进行取反即可
        '''
        single_path[list(single_path.keys())[-1]]=not single_path[list(single_path.keys())[-1]]
    return path_list

def getMemoryString(ctx, addr):
    s = str()
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s

def get_memeory_by_len(ctx,addr,length):
    s = b''
    index = 0

    while ctx.getConcreteMemoryValue(addr+index):
        c = chr(ctx.getConcreteMemoryValue(addr+index)).encode()
        s += c
        index  += 1
        length-=1
        if length <0:
            break
    return s

def getStringPosition(text):
    formatters = ['%s','%d','%#02x', '%#x', '%02x', '%x', '%*s',    \
                  '%02X', '%lX', '%ld', '%08x', '%lu', '%u', '%c']

    text = text.replace("%s", " %s ").replace("%d", " %d ").replace("%#02x", " %#02x ")   \
           .replace("%#x", " %#x ").replace("%x", " %x ").replace("%02X", " %02X ")       \
           .replace("%c", " %c ").replace("%02x", " %02x ").replace("%ld", " %ld ")       \
           .replace("%*s", " %*s ").replace("%lX", " %lX").replace("%08x", " %08x ")      \
           .replace("%u", " %u ").replace("%lu", " %lu ")                                 \


    matches = [y for x in text.split() for y in formatters if y in x]
    indexes = [index for index, value in enumerate(matches) if value == '%s']
    return indexes


def getFormatString(ctx, addr):
    return getMemoryString(ctx, addr)                                               \
           .replace("%s", "{}").replace("%d", "{:d}").replace("%#02x", "{:#02x}")   \
           .replace("%#x", "{:#x}").replace("%x", "{:x}").replace("%02X", "{:02x}") \
           .replace("%c", "{:c}").replace("%02x", "{:02x}").replace("%ld", "{:d}")  \
           .replace("%*s", "").replace("%lX", "{:x}").replace("%08x", "{:08x}")     \
           .replace("%u", "{:d}").replace("%lu", "{:d}")                            \







# Simulate the rand() function
def __rand(ctx):
    # Return value
    return random.randrange(0xffffffff)

def __memset(ctx,tainted_flag,ast):
    
    return 1, ctx

# Simulate the malloc() function
def __malloc(ctx,tainted_flag,ast):
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    print('malloc hooked')

    # Get arguments
    size = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))

    if size > mallocChunkSize:
        print('malloc failed: size too big')
        sys.exit(-1)

    if mallocCurrentAllocation >= mallocMaxAllocation:
        print('malloc failed: too many allocations done')
        sys.exit(-1)

    area = mallocBase + (mallocCurrentAllocation * mallocChunkSize)
    mallocCurrentAllocation += 1

    # Return value
    return area,ctx


# Simulate the signal() function
def __signal(ctx,tainted_flag,ast):
    print('signal hooked')

    # Get arguments
    signal  =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    handler =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))

    global sigHandlers
    sigHandlers.update({signal: handler})

    # Return value (void)
    return ctx.getConcreteRegisterValue(ctx.registers.eax)

# Simulate the strlen() function
def __strlen(ctx,tainted_flag,ast):
    print('strlen hooked')

    # Get arguments
    arg1 = getMemoryString(ctx,ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))
    '''
        这里需要注意传入内容的大小
    '''
    # Return value
    return len(arg1)


# Simulate the strtoul() function
def __strtoul(ctx,tainted_flag,ast):
    print('strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(ctx,  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))
    endptr =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))
    base   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))

    # Return value
    return int(nptr, base)

# Simulate the printf() function
def __printf(ctx,tainted_flag,ast):
    print('printf hooked')

    string_pos = getStringPosition(getMemoryString(ctx, ctx.getConcreteMemoryValue( ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteMemoryValue( ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))))
    arg2   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))
    arg3   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))
    arg4   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x10, CPUSIZE.DWORD))
    arg5   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x14, CPUSIZE.DWORD))
    arg6   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x18, CPUSIZE.DWORD))
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    esp    = ctx.getConcreteRegisterValue(ctx.registers.esp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(esp + CPUSIZE.DWORD * (i + 1), CPUSIZE.DWORD)))

    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = arg1.format(*args)
    sys.stdout.write(s)

    # Return value
    return len(s)


# Simulate the putchar() function
def __putchar(ctx,tainted_flag,ast):
    print('putchar hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue( ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def __puts(ctx,useless,ast):
    print('puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx,  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1
    
# Simulate the atoi() function
def __atoi(ctx,tainted_flag,ast):
    print('atoi hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))

    # Return value
    return int(arg1)


# Simulate the atol() function
def __atol(ctx,tainted_flag,ast):
    print('atol hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))

    # Return value
    return int(arg1)


# Simulate the atoll() function
def __atoll(ctx,tainted_flag,ast):
    print('atoll hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)))

    # Return value
    return int(arg1),ctx
def __strchr(ctx, tainted_flag, ast):
    print('strchr hooked')

    # Get arguments
    base_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp) + 0x4, CPUSIZE.DWORD))
    char_to_find = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp) + 0x8, CPUSIZE.DWORD))

    # Process the string to find the character
    current_addr = base_addr
    while True:
        current_char = ctx.getConcreteMemoryValue(MemoryAccess(current_addr, CPUSIZE.BYTE))
        if current_char == char_to_find or current_char == 0:
            break
        current_addr += 1

    # If the character is found, return the address, otherwise return NULL (0)
    return current_addr if current_char == char_to_find else 0, ctx

def __memcpy(ctx,tainted_flag,ast):
    print('memcpy hooked')

    #Get arguments
    arg1 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    arg2 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))
    arg3 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)) & 0xffffffff
    for index in range(arg3):
        value = ctx.getConcreteMemoryValue(arg2 + index)
        ctx.setConcreteMemoryValue(arg1 + index, value)
        if ctx.isMemoryTainted(arg2 + index): # 这里应该是默认按照一个字节进行设置
            ctx.taintMemory(arg1 + index)
    # 这里需要再做修改
    # if ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) or ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)),CPUSIZE.QWORD)): 
    #     ctx.taintMemory(MemoryAccess(arg1,))
    return arg1,ctx

def __ignore_func(ctx,tainted_flag,ast):
    print('useless_func hooked')

    return 0, ctx


def __strcat(ctx,tainted_flag,ast):
    print('strcat hooked')

    #Get arguments
    arg1 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    arg2 = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))

    src_length = len(getMemoryString(ctx, arg1))
    dest_length = len(getMemoryString(ctx, arg2))
    for index in range(dest_length):
        value = ctx.getConcreteMemoryValue(arg2 + index)
        ctx.setConcreteMemoryValue(arg1 + index + src_length, value)

    return arg1

# 此处用于对read函数进行摘要建模操作
def __read(ctx,tainted_flag=True,symbol_mem_map=None):
    '''
    read函数依赖的原料:
        rsi存放的是buf
        edx存放的是读入的长度
    read函数所造成的影响
    修改的寄存器:
        rax中记录的是执行read后读入的字符串的长度
        r11也会被改,但是暂时先不管为什么
    这里如果想要标记污染源可以在系统调用这里做手脚
    '''
    print('__read hooked')
    file_handle = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    # 获取缓存区地址
    target_memory=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) # 取出要输入的内容
    # 这里取出读入内容的长度readin_len
    readin_len=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))
    
    
    
    
    if symbol_mem_map is not None:
        '''
            这里说明是有东西要设置的
        '''
        addr_range=list(symbol_mem_map.keys())
        for i in range(readin_len):
            if target_memory+i in addr_range: # 如果在里面就填充解出来的内存
                ctx.setConcreteMemoryAreaValue(target_memory+i, bytes(chr(symbol_mem_map[target_memory+i]).encode()))
            else:
                # 否则就填充'a'进行代替
                ctx.setConcreteMemoryAreaValue(target_memory+i, bytes(b'a') )
    else:
        input_line = []
        # 检查当前的数据来源
        # 来自std input
        if file_handle == 0:
            # 检查当前的文件句 柄是多少
            input_line = std_input
            # 
        elif file_handle == 1:
            pass
        else:
            input_line = std_file_input
        if readin_len > 1024:
            # 这里设置
            readin_len = 1024
        if len(input_line) == 0:
            if RANDOM_INPUT:
                write_bytes = b'b'*random.randint(1,readin_len)
            else:
                raise Exception("No Enough Input for gets! Maybe you can change __config.py and set RANDOM_INPUT True.")
        else:
            write_bytes = input_line.pop()
        try:
            ctx.setConcreteMemoryAreaValue(target_memory, write_bytes) # 向目标栈地址中写入内容
        except:
            ctx.setConcreteMemoryAreaValue(target_memory, write_bytes.encode()) # 向目标栈地址中写入内容
        # 设置rax寄存器
    ctx.setConcreteRegisterValue(ctx.registers.eax, len(write_bytes))
    if True:
        # 将内存设置为符号值
        # ctx.convertMemoryToSymbolicVariable(MemoryAccess(target_memory,re_align(readin_len)))
        # 将目标区域进行污染
        ctx.taintRegister(ctx.registers.eax)

        for idx in range(readin_len):
            ctx.taintMemory(MemoryAccess(target_memory+idx,CPUSIZE.BYTE))
            ctx.symbolizeMemory(MemoryAccess(target_memory+idx,CPUSIZE.BYTE))

        # ctx.taintMemory(MemoryAccess(target_memory,re_align(readin_len)))
        # ctx.symbolizeMemory(MemoryAccess(target_memory,re_align(readin_len)))
        # expr1 = ctx.newSymbolicExpression(ast.bv(re_align(readin_len),re_align(readin_len)))
        # mem=MemoryAccess(target_memory,int(re_align(readin_len)/8))
        # ctx.assignSymbolicExpressionToMemory(expr1,mem)

    # # 取出栈顶元素
    # ctx.setConcreteRegisterValue(ctx.registers.rsp,ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD)))
    # # 栈顶指针-8
    # ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getCon   creteRegisterValue(ctx.registers.rsp)-8)
    # 设定返回值
    # print("caught read!")
    # exit()

    '''
        开始内存污染标记操作
    '''
    # 这里必须有对其长度
    # print(hex(target_memory))
    
    return len(readin_len*b'a'),ctx

# 将此处的内存按照CPU的标准进行对齐操作
def re_align(origin_size):
    # 如果原始尺寸模8余0则说明正好，不需要管
    if origin_size%16 == 0: 
        '''
            这里需要注意的是64位的CPU是按照16字节长度进行对其的
        '''
        return origin_size
    else:
        return (int(origin_size/16)+1)*16
# TODO
def __strcpy(ctx,tainted_flag,ast):
    '''
        该函数对strcpy进行建模操作
        rdi 用于存放dest地址
        rsi 用于存放source地址

        返回值：
        结束时会对r10,r11进行修改，但是暂时没有用到，先不管
        这里rdx寄存器用于接收字符串长度
        返回值是复制后的字符串指针
    '''
    source_memory=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) # 取出要输入的内容
    dest_memory=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)) # 取出要传入的内容
    # 从对应内存中取出字符串，直到读出来的内容是反斜杠00，这个用getstring能不能行
    str_=getMemoryString(ctx,source_memory) # 获取目标地址中的字符串
    ctx.setConcreteMemoryAreaValue(dest_memory, str_.encode() + b'\x00') # 向目标地址中写入该字符串
    ctx.setConcreteRegisterValue(ctx.registers.edx, len(str_)) 
    # 对污染进行传播
    for idx in range(len(str_)):
        if ctx.isMemoryTainted(source_memory+idx):
            ctx.taintMemory(dest_memory+idx)
    
    #  
    # if ctx.isRegisterTainted(ctx.registers.esi) or \
    #     ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)),CPUSIZE.DWORD)): 
    #     ctx.taintMemory(dest_memory)

    return dest_memory,ctx

def __strstr(ctx,tainted_flag, ast):
    '''
        此处堆strstr函数进行功能性建模
        string strstr(string1, string2)
        功能: strstr返回一个指针,指向string2在string1中首次出现的位置。
        返回值: string1中找到string2出现的位置
    '''
    string1_pointer = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)) # 取出要传入的内容
    string2_pointer = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) # 取出要传入的内容
    # 获取当前程序中的字符串
    string1 = getMemoryString(ctx, string1_pointer)
    string2 = getMemoryString(ctx, string2_pointer)
    # 检查是否取出正确的字符串
    if len(string1) == 0 or len(string2) == 0:
        return 0, ctx
        # raise Exception("Wrong MemPointer! No legal string Found!")
    position = string1.find(string2) # 使用Python：find() 代替C程序中的strstr find获得的位置是从0开始数的
    if position == -1:
        ctx.setConcreteRegisterValue(ctx.registers.eax, 0) 
        return 0, ctx
    else:
        ctx.setConcreteRegisterValue(ctx.registers.eax, string1_pointer+position)
        return string1_pointer+position, ctx
    

def __strncpy(ctx,tainted_flag,ast):
    '''
        该函数对strcpy进行建模操作
        注意一点 strncpy本身不具备加入反斜杠0的能力
        rdi用于记录目标地址
        rsi用于指向源地址
        rdx用于存放复制过去的字符串长度
    '''
    source_memory=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) # 取出要输入的内容
    dest_memory=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)) # 取出要传入的内容
    copy_length=ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)) # 取出要复制的长度

    
    str_=get_memeory_by_len(ctx,source_memory,copy_length) # 获取目标地址中的字符串
    ctx.setConcreteMemoryAreaValue(dest_memory, str_) # 这里注意一点strncpy本身并不会将反斜杠0加在后面
    ctx.setConcreteRegisterValue(ctx.registers.eax, dest_memory) 
    
    # 这里对目标内存进行污染操作
    if ctx.isMemoryTainted(MemoryAccess(source_memory,re_align(copy_length))):
        ctx.taintMemory(MemoryAccess(dest_memory,re_align(copy_length)))

    if ctx.isRegisterTainted(ctx.registers.esi) or ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)),CPUSIZE.QWORD)): 
        ctx.taintMemory(dest_memory)
    return dest_memory,ctx

# 设置函数
def __calloc(ctx,tainted_flag,ast):
    # calloc 两个参数rdi和rsi
    num  = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD)) # 获取内存块的个数
    size = num * ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD)) # 获取单个内存块的长度
    # calloc需要对数据进行初始化操作


    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    print('calloc hooked')


    if size > mallocChunkSize:
        print('malloc failed: size too big')
        sys.exit(-1)

    if mallocCurrentAllocation >= mallocMaxAllocation:
        print('malloc failed: too many allocations done')
        sys.exit(-1)

    area = mallocBase + (mallocCurrentAllocation * mallocChunkSize)
    mallocCurrentAllocation += 1

    return area, ctx

def __system(ctx,tainted_flag,ast):
    print('system Caught!')
    return None, ctx
def __libc_start_main(ctx,tainted_flag,ast):
    print('__libc_start_main hooked')

    # Get arguments
    main = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))

    # Push the return value to jump into the main() function
    ctx.setConcreteRegisterValue(ctx.registers.esp, ctx.getConcreteRegisterValue(ctx.registers.esp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp), CPUSIZE.QWORD)
    ctx.setConcreteMemoryValue(ret2main, main)

    # Setup target argvs
    argvs = [sys.argv[1]] + sys.argv[2:]

    # Define argc / argv
    base  = BASE_ARGV
    addrs = list()

    index = 0
    for argv in argvs:
        addrs.append(base)
        ctx.setConcreteMemoryAreaValue(base, bytes(argv.encode('utf8')) + b'\x00')

        # Tainting argvs
        for i in range(len(argv)):
            ctx.taintMemory(base + i)

        base += len(argv)+1
        # print('argv[%d] = %s' %(index, argv))
        index += 1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        ctx.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    ctx.setConcreteRegisterValue(ctx.registers.edi, argc)
    ctx.setConcreteRegisterValue(ctx.registers.esi, argv)

    return 0

def get_target_oprand(inst):
    '''
        其实这里不太需要管所有的指令，只需要管一个指令就可以了
        mov dl,source 这里是对dl进行污染了
        mov target , dl 污染自然传递不需要手动标注

        另一部分在于重入问题，第二次重入的时候，这个指令是不是还会产生污染问题？
    '''
    if len(inst.getOperands())==2: # 如果是转移指令，那么显然就是目的地址是被污染了的
        target=inst.getOperands()[0]
        if target.getType()==OPERAND.MEM:# 如果这里是一个间接寻址
            # ctx.taintMemory(target)
            # base_reg=target.getBaseRegister() # 获取基址寄存器
            # indx_reg=target.getIndexRegister() # 获取索引寄存器
            # bais_=target.getDisplacement() # 注意这里获取的内容是补码，需要做个转换
            # scale_type = target.getScale() # 这里获取的是目标内存要写入的字节长度
            # return {"base_reg":base_reg,"indx_reg":indx_reg,"bais":change_to_oppsite(bais_),"target_scale":scale_type}
            # TODO(这个后面怎么做到完整的内存标注)
            return target,1 # 这里是标注
        else:
            # 这里是目标是寄存器的时候
            target,0
    else:
        return -1,-1
def __gets(ctx,tainted_flag,ast):
    if DEBUG:
        print("gets hooked!")
    # 取出本次gets要写入的地址
    write_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    if len(std_input) == 0:
        if RANDOM_INPUT:
            write_bytes = b'b'*random.randint(1,MAX_INPUT_LEN)
        else:
            raise Exception("No Enough Input for gets! Maybe you can change __config.py and let RANDOM_INPUT be True.")
    else:
        write_bytes = std_input.pop()
    if type(write_bytes) is str:
        write_bytes=write_bytes.encode()
    ctx.setConcreteMemoryAreaValue(write_addr, write_bytes) # 向目标栈地址中写入内容
    for idx in range(len(write_bytes)):
        ctx.taintMemory(write_addr+idx)
    # 设置rax寄存器为目标值
    ctx.setConcreteRegisterValue(ctx.registers.eax, len(write_bytes))
    return len(write_bytes), ctx

def __strncmp(ctx, tainted_flag,ast):
    result = None
    str1_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    str2_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))
    size_n = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))

    string1 = getMemoryString(ctx, str1_addr)[:size_n]
    string2 = getMemoryString(ctx, str2_addr)[:size_n]
    if string1 == string2:
        result = 0
    else:
        for i in range(min(len(string1),len(string2))):
            if string1[i] != string2[i]:
                result = ord(string1[i]) - ord(string2[i])
    # 此处表示一长一短且有共同前缀
    if result is None:
        result = 0 
    ctx.setConcreteRegisterValue(ctx.registers.eax, result)
    return result,ctx

# TODO(该函数暂未实现污点传播分析的部分)
def __vsnprintf(ctx,tainted_flag,ast):
    '''
        该函数的目的是向buffer按照format的格式化字符串形式写入bufferSize大小的内容
        接收如下四个参数：
            buffer：指向目标字符数组的指针，用于存储格式化的输出结果。
            bufferSize：目标字符数组的大小，用于限制输出结果的长度。
            format：格式化字符串，指定输出的格式。
            arguments：va_list 类型的参数列表，包含了传递给格式化字符串的可变参数。
        
    '''
    if DEBUG:
        print("vsnprintf hooked!")
        
    # 要写入的缓冲区地址
    bufferAddr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))
    # 缓冲区大小
    bufferSize = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))
    # 获取格式化字符串地址
    formatString = getFormatString(ctx,ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)))
    # 从栈中取出args的参数地址
    argsAddr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x10, CPUSIZE.DWORD))
    #  获取格式化字符串
    buffer = '\x00' * bufferSize # 
    #  构造需要写入的格式化字符串
    '''
        这里取可变参数怎么整？
    '''
    # pattern = r"%(d|u|o|x|X|f|e|E|g|c|s|p|[0-9]+d|\.[0-9]+f)"
    #  查找其中的格式化表示数量
    nbArgs = formatString.count("{")
    # arg2是获取的第一个字符串的地址
    arg2   =  ctx.getConcreteMemoryValue(MemoryAccess(argsAddr, CPUSIZE.DWORD))
    arg3   =  ctx.getConcreteMemoryValue(MemoryAccess(argsAddr+0x4, CPUSIZE.DWORD))
    arg4   =  ctx.getConcreteMemoryValue(MemoryAccess(argsAddr+0x8, CPUSIZE.DWORD))
    arg5   =  ctx.getConcreteMemoryValue(MemoryAccess(argsAddr+0xc, CPUSIZE.DWORD))
    arg6   =  ctx.getConcreteMemoryValue(MemoryAccess(argsAddr+0x10, CPUSIZE.DWORD))
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    source_address =  deepcopy(args)
    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(argsAddr + CPUSIZE.DWORD * (i + 1), CPUSIZE.DWORD)))
    # 获取字符串中的位置
    string_pos = getStringPosition(getMemoryString(ctx,ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))))
    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = formatString.format(*args)
    for c_idx in range(len(args)):
        ctx.setConcreteMemoryValue(bufferAddr+c_idx,ord(s[c_idx]))
        if ctx.isMemoryTainted(source_address[c_idx]):
            #  设置污染传播
            ctx.taintMemory(bufferAddr+c_idx)
    ctx.setConcreteRegisterValue(ctx.registers.eax, len(s))
    #  返回写入的字符数
    return len(s),ctx
# Simulate the snprintf function
def __snprintf(ctx, tainted_flag, ast):
    print('snprintf hooked')

    # Get arguments
    esp = ctx.getConcreteRegisterValue(ctx.registers.esp)
    # First argument - destination buffer
    dst_addr = ctx.getConcreteMemoryValue(MemoryAccess(esp + 0x4, CPUSIZE.DWORD))
    # Second argument - maximum size of the buffer
    max_size = ctx.getConcreteMemoryValue(MemoryAccess(esp + 0x8, CPUSIZE.DWORD))
    # Third argument - format string
    # Assume format string is directly after the max_size on the stack
    format_addr = ctx.getConcreteMemoryValue(MemoryAccess(esp + 0xC, CPUSIZE.DWORD))
    format_str = getBUILDMemoryString(format_addr,ctx)

    # Simulate variadic arguments handling by reading stack values after the format string
    # Depending on your use case, you might have to handle this more robustly
    arg_list = []
    arg_start = esp + 0x10  # After format_addr
    while True:
        arg = ctx.getConcreteMemoryValue(MemoryAccess(arg_start, CPUSIZE.DWORD))
        arg_list.append(arg)
        arg_start += 4
        if len(arg_list) == MAX_ARGS or some_condition_to_stop:
            break

    # Simulate the snprintf behavior
    # You might need a more sophisticated way to handle the actual formatting
    # This is a simplified simulation assuming all arguments are integers
    formatted_str = format_str % tuple(arg_list[:format_str.count("%")])
    truncated_str = formatted_str[:max_size - 1] + '\0'

    # Write the formatted string to destination
    writeMemoryString(dst_addr, truncated_str,ctx)

    # Return value is the number of characters written (excluding null byte)
    return len(truncated_str) - 1

# Helper function to write a string to memory in Triton
def writeMemoryString(address, string,ctx):
    for i, c in enumerate(string):
        ctx.setConcreteMemoryValue(MemoryAccess(address + i, CPUSIZE.BYTE), ord(c))

# Helper function to get a string from memory in Triton
def getBUILDMemoryString(address,ctx):
    string = ''
    c = ctx.getConcreteMemoryValue(MemoryAccess(address, CPUSIZE.BYTE))
    while c != 0:
        string += chr(c)
        address += 1
        c = ctx.getConcreteMemoryValue(MemoryAccess(address, CPUSIZE.BYTE))
    return string
def __strcasecmp(ctx,tainted_flag, ast):
    return 1, ctx
# Your code should have a MAX_ARGS constant or a condition to stop
# reading arguments to avoid infinite loops
MAX_ARGS = 10  # You can adjust this

'''
    sprin
'''
def __sprintf(ctx,tainted,ast):
    # 这里是最终要写入的部分
    string_pos = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x4, CPUSIZE.DWORD))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteMemoryValue( ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x8, CPUSIZE.DWORD))))
    arg2   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD))
    arg3   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x10, CPUSIZE.DWORD))
    arg4   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x14, CPUSIZE.DWORD))
    arg5   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x18, CPUSIZE.DWORD))
    arg6   =  ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0x1c, CPUSIZE.DWORD))
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    esp    = ctx.getConcreteRegisterValue(ctx.registers.esp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(esp + CPUSIZE.DWORD * (i + 1), CPUSIZE.DWORD)))
    s = arg1.format(*args)
    count = 0
    for per_c in s:
        ctx.setConcreteMemoryValue(string_pos+count,per_c.encode())
        if ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp)+0xc, CPUSIZE.DWORD)):
            ctx.taintMemory(string_pos+count)
        count+=1
    # 这里开始

    # Return value
    return len(s),ctx
def __execl(ctx, tainted,ast):
    print("Got! Execl")
    return 1,ctx

def __dup2(ctx, tainted,ast):
    print("Got! dup2")
    return 1,ctx
# Assume some_condition_to_stop is a condition defined by you
# to stop reading arguments for the format string
some_condition_to_stop = False 
customRelocation32 = [
    ['printf',            __printf,             None],
    ['__libc_start_main', __libc_start_main,    None],
    ['putchar',           __putchar,            None],
    ['puts',              __puts,               None],
    ['read',              __read,               None],
    ['_read',              __read,              None],
    ['atol',              __atol,               None],
    ['atoll',             __atoll,              None],
    ['malloc',            __malloc,             None],
    ['memcpy',            __memcpy,             None],
    ['strcpy',            __strcpy,             None],
    ['strncpy',            __strncpy,           None],
    ['rand',              __rand,               None],
    ['signal',            __signal,             None],
    ['strcat',            __strcat,             None],
    ['strlen',            __strlen,             None],
    ['strtoul',           __strtoul,            None],
    ['system',           __system,              None],
    ['calloc',            __calloc,             None],
    ['gst_buffer_unmap',  __ignore_func,        None],
    ['gst_buffer_map',   __ignore_func,         None],
    ['gets',             __gets,                None],   
    ['strstr',          __strstr,               None],
    ['vsnprintf',        __vsnprintf,           None],
    ['gst_pad_push',     __ignore_func,         None],
    ['g_free',            __ignore_func,        None],
    ['g_malloc',            __ignore_func,      None],
    ['gst_adapter_available', __ignore_func,    None],
    ['strncmp',         __strncmp,              None],
    ['strchr',          __strchr,               None],
    ['snprintf',        __snprintf,             None],
    ['pthread_self',    __ignore_func,          None],
    ['memset',          __memset,               None],
    ['strcasecmp',      __strcasecmp,           None],
    ['getenv',          __ignore_func,          None],
    ['time',            __ignore_func,          None],
    ['srandom',         __ignore_func,            None],
    ['gethostbyname2',  __ignore_func,          None],
    ['fprintf',        __ignore_func,           None],
    ['__memcpy_chk',     __memcpy,                None],
    ['write',          __ignore_func,           None],
    ['vfprintf',       __ignore_func,           None],
    ['free',           __ignore_func,            None],
    ['have_custom_cols', __ignore_func,          None],
    ['epan_dissect_init', __ignore_func,         None],
    ['epan_dissect_run', __ignore_func,          None],
    ['epan_dissect_cleanup',  __ignore_func,     None],
    ['_setjmp',            __ignore_func,       None],
    ['setjmp',            __ignore_func,       None],
    ['g_slice_alloc',     __malloc,            None],
    ['g_slist_append',    __ignore_func,       None],
    ['g_hash_table_lookup', __ignore_func,     None],
    ['localtime',         __ignore_func,       None],
    ['strftime',          __ignore_func,       None],
    ['sprintf',           __sprintf,           None],
    ['fopen',             __ignore_func,        None],
    ['fputs',             __ignore_func,        None],
    ['fclose',            __ignore_func,        None],
    ['_xstat',           __ignore_func,         None],
    ['xstat',            __ignore_func,          None],
    ['__xstat',           __ignore_func,         None],
    ['setbuf',           __ignore_func,          None],
    ['chdir',            __ignore_func,          None],
    ['execl',            __execl,          None],
    ['send',             __ignore_func,          None],
    ['dup2',             __dup2,          None],
    ['scandir',          __ignore_func,         None],
    ['close',            __ignore_func,         None],
    ['select',          __ignore_func,          None],
    ['inet_ntoa',        __ignore_func,         None],
    ['__xstat',         __ignore_func,          None],

    # ['memmove',       __memcpy,                 None] # 如果是跑latex则删除该建模
]