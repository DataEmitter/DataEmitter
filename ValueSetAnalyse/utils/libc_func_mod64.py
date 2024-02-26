from copy import copy,deepcopy
import sys
import string
import random
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND
from config import *
BASE_PLT   = 0x10000000
BASE_ARGV  = 0x20000000
BASE_ALLOC = 0x30000000
BASE_STACK = 0x9ffffff0


mallocCurrentAllocation = 0
mallocMaxAllocation     = 2048
mallocBase              = BASE_ALLOC
mallocChunkSize         = 0x00010000
#  从列表中随机抽取n个元素
def random_sample(lst, n):
    sampled = random.choices(lst, k=n)
    return ''.join(sampled).encode()

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
    pass

# Simulate the malloc() function
def __malloc(ctx,tainted_flag,ast):
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    print('malloc hooked')

    # Get arguments
    size = ctx.getConcreteRegisterValue(ctx.registers.rdi)

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

# Simulate the realloc() function
def __realloc(ctx,tainted_flag,ast):
    global mallocCurrentAllocation
    global mallocMaxAllocation
    global mallocBase
    global mallocChunkSize

    print('realloc hooked')

    # Get arguments
    ptr = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    new_size = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    if new_size > mallocChunkSize:
        print('realloc failed: size too big')
        sys.exit(-1)

    if mallocCurrentAllocation >= mallocMaxAllocation:
        print('realloc failed: too many allocations done')
        sys.exit(-1)

    # Compute the new area
    area = mallocBase + (mallocCurrentAllocation * mallocChunkSize)
    mallocCurrentAllocation += 1

    # Copy the old data into the new area
    old_area = ptr
    byte_size = min(new_size, mallocChunkSize)  # Copy up to new_size bytes or size of old_chunk, whichever is smaller
    for i in range(byte_size):
        value = ctx.getConcreteMemoryValue(old_area + i)
        ctx.setConcreteMemoryValue(area + i, value)
    # Return the new area
    return area, ctx

# Simulate the signal() function
def __signal(ctx,tainted_flag,ast):
    print('signal hooked')

    # Get arguments
    signal  = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    handler = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    global sigHandlers
    sigHandlers.update({signal: handler})

    # Return value (void)
    return ctx.getConcreteRegisterValue(ctx.registers.rax)

# Simulate the strlen() function
def __strlen(ctx,tainted_flag,ast):
    print('strlen hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return len(arg1)


# Simulate the strtoul() function
def __strtoul(ctx,tainted_flag,ast):
    print('strtoul hooked')

    # Get arguments
    nptr   = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    endptr = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    base   = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    # Return value
    return int(nptr, base)

# Simulate the printf() function
def __printf(ctx,tainted_flag,ast):
    print('printf hooked')

    string_pos = getStringPosition(getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi)))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg6   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    rsp    = ctx.getConcreteRegisterValue(ctx.registers.rsp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(rsp + CPUSIZE.QWORD * (i + 1), CPUSIZE.QWORD)))

    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = arg1.format(*args)
    sys.stdout.write(s)

    # Return value
    return len(s),ctx
def __fprintf(ctx,tainted_flag, ast):
    print('fprintf hooked')

    string_pos = getStringPosition(getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rsi)))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rsi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5][:nbArgs]
    rsp    = ctx.getConcreteRegisterValue(ctx.registers.rsp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(rsp + CPUSIZE.QWORD * (i + 1), CPUSIZE.QWORD)))

    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = arg1.format(*args)
    sys.stdout.write(s)

    # Return value
    return len(s),ctx

def __vfprintf(ctx,tainted_flag, ast):
    print('fprintf hooked')

    string_pos = getStringPosition(getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rsi)))

    # Get arguments
    arg1   = getFormatString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rsi))
    arg2   = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    arg3   = ctx.getConcreteRegisterValue(ctx.registers.rcx)
    arg4   = ctx.getConcreteRegisterValue(ctx.registers.r8)
    arg5   = ctx.getConcreteRegisterValue(ctx.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5][:nbArgs]
    rsp    = ctx.getConcreteRegisterValue(ctx.registers.rsp)

    if nbArgs > 5:
        for i in range(nbArgs - 5):
            args.append(ctx.getConcreteMemoryValue(MemoryAccess(rsp + CPUSIZE.QWORD * (i + 1), CPUSIZE.QWORD)))

    for i in string_pos:
        args[i] = getMemoryString(ctx, args[i])
    s = arg1.format(*args)
    sys.stdout.write(s)

    # Return value
    return len(s),ctx

# Simulate the putchar() function
def __putchar(ctx,tainted_flag,ast):
    print('putchar hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1) + '\n')

    # Return value
    return 2


# Simulate the puts() function
def __puts(ctx,useless,ast):
    print('puts hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1 + '\n')

    # Return value
    return len(arg1) + 1
    
# Simulate the atoi() function
def __atoi(ctx,tainted_flag,ast):
    print('atoi hooked')

    # Get arguments
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)


# Simulate the atol() function
def __atol(ctx,tainted_flag,ast):
    print('atol hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)


# Simulate the atoll() function
def __atoll(ctx,tainted_flag,ast):
    print('atoll hooked')

    # Get arguments
    arg1 = getMemoryString(ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Return value
    return int(arg1)

def __memcpy(ctx,tainted_flag,ast):
    print('memcpy hooked')

    #Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    arg3 = ctx.getConcreteRegisterValue(ctx.registers.rdx) & 0xffffffff
    for index in range(arg3):
        value = ctx.getConcreteMemoryValue(arg2 + index)
        ctx.setConcreteMemoryValue(arg1 + index, value)
        if ctx.isMemoryTainted(arg2 + index): # 这里应该是默认按照一个字节进行设置
            ctx.taintMemory(arg1 + index)
    if ctx.isRegisterTainted(ctx.registers.rsi) or ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi),CPUSIZE.QWORD)): 
        ctx.taintMemory(arg1)
    return arg1,ctx

def __bsearch(ctx, tainted_flag, ast):
    print('bsearch hooked')

    # Get arguments
    key = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    base = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    nitems = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    size = ctx.getConcreteRegisterValue(ctx.registers.rcx)

    # Searching
    for i in range(nitems):
        # Supposing all elements are integers
        candidate = ctx.getConcreteMemoryValue(base + i * size)
        
        if candidate == key:  # if the candidate matches the key
            result_value = candidate
            break
    else:  # if no candidate matches the key
        result_value = 0  # NULL

    # Taint the key if any candidate (or the base) is tainted
    if any(ctx.isMemoryTainted(base + i * size) for i in range(nitems)):
        ctx.taintRegister(ctx.registers.rdi)

    # Return value
    return result_value, ctx
import math

def __exp(ctx, tainted_flag, ast):
    print('exp hooked')

    # Get argument
    # Assuming the argument `x` is passed in a floating-point register (like xmm0)
    x = ctx.getConcreteRegisterValue(ctx.registers.xmm0)

    # Compute exponential
    result_value = math.exp(x)

    # Check if the input x is tainted, and if so, taint the result
    if ctx.isRegisterTainted(ctx.registers.xmm0):
        ctx.taintRegister(ctx.registers.xmm0)

    # Return the result value
    # Depending on the calling convention, set the right register or memory location
    ctx.setConcreteRegisterValue(ctx.registers.xmm0, result_value)

    return result_value, ctx

def __memset(ctx, tainted_flag, ast):
    print('memset hooked')

    # Get arguments
    dest_addr = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    char_value = ctx.getConcreteRegisterValue(ctx.registers.rsi) & 0xff  # Ensure it is a single byte value
    num_bytes = ctx.getConcreteRegisterValue(ctx.registers.rdx) & 0xffffffff

    # Set 'num_bytes' memory bytes to 'char_value' starting at 'dest_addr'
    for index in range(num_bytes):
        ctx.setConcreteMemoryValue(dest_addr + index, char_value)

        # If tainted_flag is True, propagate the taint.
        if tainted_flag:
            ctx.taintMemory(dest_addr + index)

    # Taint destination if either destination is already tainted
    # or if 'char_value' is tainted.
    if ctx.isMemoryTainted(dest_addr) or ctx.isRegisterTainted(ctx.registers.rsi):
        ctx.taintMemory(dest_addr)

    return dest_addr,ctx


def __ignore_func(ctx,tainted_flag,ast):
    print('useless_func hooked')

    return 0, ctx


def __strcat(ctx):
    print('strcat hooked')

    #Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)

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
    global std_input
    # 获取缓存区地址
    target_memory=ctx.getConcreteRegisterValue(ctx.registers.rsi) # 取出要输入的内容
    # 这里取出读入内容的长度readin_len
    readin_len=ctx.getConcreteRegisterValue(ctx.registers.rdx) 
    new_len = readin_len
    if symbol_mem_map is not None and len(std_input) == 0 :
        '''
            这里说明是有东西要设置的
        '''
        addr_range=list(symbol_mem_map.keys())
        for i in range(readin_len):
            if target_memory+i in addr_range: # 如果在里面就填充解出来的内存
                ctx.setConcreteMemoryAreaValue(target_memory+i, bytes(chr(symbol_mem_map[target_memory+i]).encode()))
            else:
                # 否则就使用随机输入进行代替
                ctx.setConcreteMemoryAreaValue(target_memory+i, bytes(random_sample(word_list,1)) )

        ctx.setConcreteRegisterValue(ctx.registers.rax, readin_len)
        
    elif len(std_input) != 0:
        inpt_string = std_input.pop()
        for i in range(len(inpt_string)):
            # 这里直接写入内存
            ctx.setConcreteMemoryAreaValue(target_memory+i, bytes(list(inpt_string)[i].encode()))
        ctx.setConcreteRegisterValue(ctx.registers.rax, len(inpt_string))
        new_len = len(inpt_string)
    else:
    # 向缓存区中写入内容
        ctx.setConcreteMemoryAreaValue(target_memory, bytes(random_sample(word_list,readin_len)) ) # 向目标栈地址中写入内容
        # 设置rax寄存器
        ctx.setConcreteRegisterValue(ctx.registers.rax, readin_len)
    ctx.taintRegister(ctx.registers.rax)

    for idx in range(new_len):
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
    return new_len,ctx

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
    source_memory=ctx.getConcreteRegisterValue(ctx.registers.rsi) # 取出要输入的内容
    dest_memory=ctx.getConcreteRegisterValue(ctx.registers.rdi) # 取出要传入的内容
    # 从对应内存中取出字符串，直到读出来的内容是反斜杠00，这个用getstring能不能行
    str_=getMemoryString(ctx,source_memory) # 获取目标地址中的字符串
    ctx.setConcreteMemoryAreaValue(dest_memory, bytes(str_) + b'\x00') # 向目标地址中写入该字符串
    ctx.setConcreteRegisterValue(ctx.registers.rdx, len(str_)) 

    if ctx.isRegisterTainted(ctx.registers.rsi) or ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi),CPUSIZE.QWORD)): 
        ctx.taintMemory(dest_memory)

    return dest_memory,ctx

def __strncpy(ctx,tainted_flag,ast):
    '''
        该函数对strcpy进行建模操作
        注意一点 strncpy本身不具备加入反斜杠0的能力
        rdi用于记录目标地址
        rsi用于指向源地址
        rdx用于存放复制过去的字符串长度
    '''
    source_memory=ctx.getConcreteRegisterValue(ctx.registers.rsi) # 取出要输入的内容
    dest_memory=ctx.getConcreteRegisterValue(ctx.registers.rdi) # 取出要传入的内容
    copy_length=ctx.getConcreteRegisterValue(ctx.registers.rdx) # 取出要复制的长度

    
    str_=get_memeory_by_len(ctx,source_memory,copy_length) # 获取目标地址中的字符串
    ctx.setConcreteMemoryAreaValue(dest_memory, str_) # 这里注意一点strncpy本身并不会将反斜杠0加在后面
    ctx.setConcreteRegisterValue(ctx.registers.rax, dest_memory) 

    # 这里对目标内存进行污染操作
    if ctx.isMemoryTainted(MemoryAccess(source_memory,copy_length)):
        ctx.taintMemory(MemoryAccess(dest_memory,copy_length))

    if ctx.isRegisterTainted(ctx.registers.rsi) or ctx.isMemoryTainted(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsi),CPUSIZE.QWORD)): 
        ctx.taintMemory(dest_memory)
    return dest_memory,ctx

# 设置函数
def __calloc(ctx,tainted_flag,ast):
    # calloc 两个参数rdi和rsi
    num  = ctx.getConcreteRegisterValue(ctx.registers.rdi) # 获取内存块的个数
    size = num * ctx.getConcreteRegisterValue(ctx.registers.rsi) # 获取单个内存块的长度
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
    main = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Push the return value to jump into the main() function
    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD)
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

    ctx.setConcreteRegisterValue(ctx.registers.rdi, argc)
    ctx.setConcreteRegisterValue(ctx.registers.rsi, argv)

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
# 进行内容的发送
def __send(ctx,tainted_flag,ast):
    return ctx.getConcreteRegisterValue(ctx.registers.rdi), ctx

def __stack_chk_fail(ctx, tainted_flag,ast):
    print("STACK CHECK FAILED!")
    return 0xdeadbeef, ctx

def strtol(str, endptr, base=10):
    # 跳过字符串开头的空白字符
    str = str.strip()

    # 初始化指针位置
    ptr = 0

    # 检查是否存在符号位
    sign = 1
    if str[ptr] == '+' or str[ptr] == '-':
        if str[ptr] == '-':
            sign = -1
        ptr += 1

    # 检查是否存在基数前缀
    if base == 0:
        if str[ptr:ptr+2] == '0x' or str[ptr:ptr+2] == '0X':
            base = 16
            ptr += 2
        elif str[ptr] == '0':
            base = 8
            ptr += 1
        else:
            base = 10

    # 转换数字部分
    num = 0
    while ptr < len(str) and str[ptr].isdigit() or (base == 16 and str[ptr].isalpha()):
        if base == 16 and str[ptr].isalpha():
            digit = int(str[ptr], 16)
        else:
            digit = int(str[ptr])
        num = num * base + digit
        ptr += 1

    # 更新 endptr 的值
    if endptr is not None:
        *endptr, = str[ptr:]

    # 返回最终结果
    return sign * num

def __strtol(ctx, tainted_flag, ast):
    '''
        该函数对strtol进行建模操作
        rdi用于记录要转换的字符串的地址
        rsi用于记录endptr的地址
        rdx用于记录转换时采用的进制
    '''
    str_memory = ctx.getConcreteRegisterValue(ctx.registers.rdi)  # 取出要转换的字符串地址
    endptr_memory = ctx.getConcreteRegisterValue(ctx.registers.rsi)  # 取出endptr的地址
    base = ctx.getConcreteRegisterValue(ctx.registers.rdx)  # 取出转换时使用的进制

    # 从内存中获取要转换的字符串
    str_ = getMemoryString(ctx, str_memory)

    # 将字符串转换为长整型
    try:
        result = int(str_, base)
    except ValueError:
        result = 0

    # 设置返回值
    ctx.setConcreteRegisterValue(ctx.registers.rax, result)

    # 如果原字符串是污染的，则污染结果
    if ctx.isMemoryTainted(MemoryAccess(str_memory, CPUSIZE.WORD)):
        ctx.taintMemory(MemoryAccess(ctx.registers.rax, CPUSIZE.QWORD))

    # 更新endptr的值，这里简化处理，可能需要更精确的逻辑来决定endptr的值
    if endptr_memory != 0:
        ctx.setConcreteMemoryValue(MemoryAccess(endptr_memory, CPUSIZE.QWORD), str_memory + len(str_))

    return result, ctx

def __atoi(ctx, tainted_flag, ast):
    '''
        本函数对 atoi 函数进行建模操作
        rdi 用于记录要转换的字符串的地址
    '''

    str_memory = ctx.getConcreteRegisterValue(ctx.registers.rdi)  # 从寄存器取出要转换的字符串地址

    # 从内存中获取要转换的字符串
    str_ = getMemoryString(ctx, str_memory)

    # 将字符串转换为整数
    try:
        result = int(str_)
    except ValueError:
        result = 0

    # 设置返回值
    ctx.setConcreteRegisterValue(ctx.registers.rax, result)

    # 如果原字符串是污染的，则污染结果
    if ctx.isMemoryTainted(MemoryAccess(str_memory, CPUSIZE.BYTE)):
        # 如果原本的内存是受污染的，那就设置寄存器
        ctx.taintRegister(ctx.registers.rax)

    return result, ctx

def __setvbuf(ctx, tainted_flag, ast):
    return 0,ctx
def __alarm(ctx, tainted_flag, ast):
    return 0,ctx

def __strcmp(ctx, tainted_flag, ast):
    '''
        本函数对 strcmp 函数进行建模操作
        rdi 用于记录第一个字符串的地址
        rsi 用于记录第二个字符串的地址
    '''

    str1_memory = ctx.getConcreteRegisterValue(ctx.registers.rdi)  # 取出第一个字符串的地址
    str2_memory = ctx.getConcreteRegisterValue(ctx.registers.rsi)  # 取出第二个字符串的地址

    # 从内存中获取两个字符串
    str1 = getMemoryString(ctx, str1_memory)
    str2 = getMemoryString(ctx, str2_memory)

    # 比较字符串并设置返回值，如果 str1 < str2，返回负值；如果 str1 = str2，返回0；如果 str1 > str2，返回正值
    if str1 < str2:
        result = -1
    elif str1 == str2:
        result = 0
    else:
        result = 1

    ctx.setConcreteRegisterValue(ctx.registers.rax, result)

    # 如果任意一个原字符串是污染的，则污染结果
    if ctx.isMemoryTainted(MemoryAccess(str1_memory, CPUSIZE.WORD)) or ctx.isMemoryTainted(MemoryAccess(str2_memory, CPUSIZE.WORD)):
        ctx.taintMemory(MemoryAccess(ctx.registers.rax, CPUSIZE.QWORD))

    return result, ctx
# poll
def __poll(ctx, tainted_flag, ast):
    '''
        这里的poll主要用于对程序中的内容进行建模,
    '''
    fd_struct = ctx.getConcreteRegisterValue(ctx.registers.rdi) # 获取对应的文件结构体
    # 设置实际发生的事件
    ctx.setConcreteMemoryValue(MemoryAccess(fd_struct + 0x6, CPUSIZE.BYTE), 0x1)
    ctx.setConcreteRegisterValue(ctx.registers.rax, 1)
    return 1,ctx

# 这里进行粗糙的建模
def __clock_gettime(ctx, tainted_flag, ast):
    '''
        对 clock_gettime 函数进行建模操作
        rdi 用于记录 clockid_t 类型的 clk_id
        rsi 用于记录要填充的 timespec 结构体的地址
    '''

    res_memory = ctx.getConcreteRegisterValue(ctx.registers.rsi)  # 从寄存器取出 timespec 结构体地址

    # 假设我们返回的时间是 10 秒 500 纳秒
    seconds = 10
    nanoseconds = 500

    # 将这些值写入 res_memory 指向的内存中
    ctx.setConcreteMemoryValue(MemoryAccess(res_memory, CPUSIZE.QWORD), seconds)
    ctx.setConcreteMemoryValue(MemoryAccess(res_memory + 8, CPUSIZE.QWORD), nanoseconds)  # 指向秒和纳秒相差8个字节

    # 一切顺利，所以函数返回值为0
    ctx.setConcreteRegisterValue(ctx.registers.rax, 0)

    # 如果 clk_id 或者 res 是有污点的，那么我们标记返回的秒和纳秒也带有污点
    if ctx.isRegisterTainted(ctx.registers.rdi) or ctx.isRegisterTainted(ctx.registers.rsi):
        ctx.taintMemory(MemoryAccess(res_memory, CPUSIZE.QWORD))
        ctx.taintMemory(MemoryAccess(res_memory + 8, CPUSIZE.QWORD))

    return 0, ctx
def __recv(ctx, tainted_flag, ast):
    dest_memory = ctx.getConcreteRegisterValue(ctx.registers.rsi)  # 取出要写入的目标地址
    read_len = ctx.getConcreteRegisterValue(ctx.registers.rdx)  # 要写入的内容长度
    for idx in range(read_len):
        # 这里设置为默认0x1
        ctx.setConcreteMemoryValue(MemoryAccess(dest_memory + idx, CPUSIZE.BYTE), 0x1)
        # 设置污染值
        ctx.taintMemory(MemoryAccess(dest_memory+idx,CPUSIZE.BYTE))
        ctx.symbolizeMemory(MemoryAccess(dest_memory+idx,CPUSIZE.BYTE))
    # 读入内容长度为返回值
    ctx.setConcreteRegisterValue(ctx.registers.rax, read_len)
    return read_len, ctx

def __putc(ctx, tainted_flag, ast):
    print("putc Hooked!")
    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    sys.stdout.write(chr(arg1) + '\n')
    return 1, ctx

def __fwrite(ctx, tainted_flag, ast):
    print("fwrite Hooked!")
    arg1 = getMemoryString(ctx, ctx.getConcreteRegisterValue(ctx.registers.rdi))
    sys.stdout.write(arg1)
    return len(arg1)

'''
    下面是让GPT帮忙建的模
'''
import os
def __access(ctx, tainted_flag, ast):
    print('access hooked')

    # Get arguments
    filepath = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    mode = ctx.getConcreteRegisterValue(ctx.registers.rsi)

    # Simulate file access check (Note: In a real hook, you would somehow simulate this)
    result = os.access(filepath, mode)
    # 这里设置返回值
    ctx.setConcreteRegisterValue(ctx.registers.rax,result)
    # Return value (In a real hook, the result might be converted into a register value)
    return result, ctx

def __isalpha(ctx, tainted_flag, ast):
    print('isalpha hooked')

    # Get argument
    char = chr(ctx.getConcreteRegisterValue(ctx.registers.rdi))

    # Check if the character is alphabetic
    result = char.isalpha()
    ctx.setConcreteRegisterValue(ctx.registers.rax,int(result))
    # Convert boolean result to an integer
    return int(result), ctx

def __floor(ctx, tainted_flag, ast):
    print('floor hooked')

    # Get argument
    x = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Compute floor
    result = math.floor(x)
    ctx.setConcreteRegisterValue(ctx.registers.rax,result)
    # Return value
    return result, ctx

def __memmove(ctx, tainted_flag, ast):
    print('memmove hooked')

    # Get arguments
    dest = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    src = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    count = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    # Simulate memory move
    for index in range(count):
        value = ctx.getConcreteMemoryValue(src + index)
        ctx.setConcreteMemoryValue(dest + index, value)
        if ctx.isMemoryTainted(src + index):
            ctx.taintMemory(dest + index)

    # Return destination address
    return dest, ctx

def __toupper(ctx, tainted_flag, ast):
    print('toupper hooked')

    # Get argument
    char = chr(ctx.getConcreteRegisterValue(ctx.registers.rdi))
    
    # Convert to uppercase
    result = ord(char.upper())
    ctx.setConcreteRegisterValue(ctx.registers.rax,result)
    # Return value
    return result, ctx

def __mkdir(ctx, tainted_flag, ast):
    print('mkdir hooked')

    # Get arguments
    path = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    mode = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    os.mkdir(path)
    # Simulate directory creation (This code would not actually create a directory)
    result = 0  # Success; in real use, you'd check success of syscall or direct call

    # Return value
    return result, ctx

def __strtok(ctx, tainted_flag, ast):
    print('strtok hooked')
    # strtok functionality is complex to replicate as it maintains internal state
    # for simplicity, we'll just demonstrate argument retrieval as an example
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    # Further processing would be needed here for accurate modeling
    return arg1, ctx

def __getcwd(ctx, tainted_flag, ast):
    print('getcwd hooked')
    raise Exception("GetCWD!!!!!!!!!!!!!!!")
    # Get arguments
    buffer = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    size = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    # Simulate getcwd (This code doesn't actually get the cwd)
    result = 0  # Pointer to the buffer; in real use, fill buffer with cwd path and null-terminate

    # Return value
    return result, ctx
def __pow(ctx, tainted_flag, ast):
    print('pow hooked')
    # Assume RDI contains the base and RSI contains the exponent
    base = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    exponent = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    # Here we can simulate a simple pow operation, though in reality you'd use more complex FPU state
    result = base ** exponent
    # For simplicity, we're placing the result back into RDI
    ctx.setConcreteRegisterValue(ctx.registers.rdi, result)
    return result, ctx
import time
def __localtime(ctx, tainted_flag, ast):
    print('localtime hooked')
    time_t_pointer = time.time()

    # Simulate the conversion of time_t to struct tm
    # You can replace this placeholder implementation with your own logic
    tm_sec = time_t_pointer % 60
    tm_min = (time_t_pointer // 60) % 60
    tm_hour = (time_t_pointer // 3600) % 24
    tm_mday = (time_t_pointer // (3600 * 24)) % 31 + 1
    tm_mon = (time_t_pointer // (3600 * 24 * 31)) % 12 + 1
    tm_year = (time_t_pointer // (3600 * 24 * 31 * 12)) + 1970 - 1900

    # Create a struct tm object in memory
    tm_struct_pointer = ctx.getConcreteRegisterValue(ctx.registers.rdi)

    # Write struct tm members to memory
    ctx.setConcreteMemoryValue(tm_struct_pointer + 0, int(tm_sec))
    ctx.setConcreteMemoryValue(tm_struct_pointer + 4, int(tm_min))
    ctx.setConcreteMemoryValue(tm_struct_pointer + 8, int(tm_hour))
    ctx.setConcreteMemoryValue(tm_struct_pointer + 12, int(tm_mday))
    ctx.setConcreteMemoryValue(tm_struct_pointer + 16, int(tm_mon))
    ctx.setConcreteMemoryValue(tm_struct_pointer + 20, int(tm_year))

    return tm_struct_pointer, ctx



def __memrchr(ctx, tainted_flag, ast):
    print('memrchr hooked')
    # Get the block of memory, the character to find and the block size
    block = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    character = ctx.getConcreteRegisterValue(ctx.registers.rsi) & 0xff
    size = ctx.getConcreteRegisterValue(ctx.registers.rdx)

    # Go through the block backwards to find the character
    address = None
    for offset in reversed(range(0, size)):
        if ctx.getConcreteMemoryValue(block + offset) == character:
            address = block + offset
            break

    # Return the address if the character was found or NULL otherwise
    # According to the C standard, we should return a void pointer, so cast it to an integer
    ctx.setConcreteRegisterValue(ctx.registers.rax, address if address is not None else 0)
    return address, ctx

def __islower(ctx, tainted_flag, ast):
    print('islower hooked')
    # The islower function checks if a character is a lowercase letter
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi) & 0xff
    # Simplified check - this does not cover localization or other checks
    result = 1 if 'a' <= chr(arg1) <= 'z' else 0
    ctx.setConcreteRegisterValue(ctx.registers.rax, result)
    return result, ctx

def __strtoll(ctx, tainted_flag, ast):
    print('strtoll hooked')
    # Retrieve the string pointer and the endptr pointer (if it exists)
    string_ptr = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    endptr = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    base = ctx.getConcreteRegisterValue(ctx.registers.rdx)
    # Please note that we are not handling the entire complexity of strtoll
    # We assume the string ends with a null byte for simplicity
    string = b''
    while True:
        char = ctx.getConcreteMemoryValue(string_ptr)
        string_ptr += 1
        if char == 0:
            break
        string += bytes([char])

    value_str = string.decode()
    try:
        value = int(value_str, base)
        ctx.setConcreteRegisterValue(ctx.registers.rax, value)
        if endptr != 0:
            ctx.setConcreteMemoryValue(endptr, string_ptr - 1)  # Point to the null terminator
    except ValueError:
        ctx.setConcreteRegisterValue(ctx.registers.rax, 0)
        if endptr != 0:
            ctx.setConcreteMemoryValue(endptr, endptr)  # If conversion fails, endptr stores the address of the string

    return value, ctx

def __strncat(ctx, tainted_flag, ast):
    print('strncat hooked')
    # Get start of destination and source strings
    dest = ctx.getConcreteRegisterValue(ctx.registers.rdi)
    src = ctx.getConcreteRegisterValue(ctx.registers.rsi)
    n = ctx.getConcreteRegisterValue(ctx.registers.rdx)
   
    # Find end of dest string
    end_dest = dest
    while ctx.getConcreteMemoryValue(end_dest) != 0x00:
        end_dest += 1
    
    # Start copying
    for i in range(n):
        char = ctx.getConcreteMemoryValue(src + i)
        ctx.setConcreteMemoryValue(end_dest + i, char)
        if char == 0x00:
            break

    if i != n-1:  # Append null byte if not done in loop
        ctx.setConcreteMemoryValue(end_dest + n, 0x00)

    return dest, ctx
import ctypes
import struct
def __strftime(ctx, tainted_flag, ast):
    print('strftime hooked')

    # Get arguments
    arg1 = ctx.getConcreteRegisterValue(ctx.registers.rdi) # Buffer for storing the returned string
    arg2 = ctx.getConcreteRegisterValue(ctx.registers.rsi) # Maximum size of the string
    arg3 = ctx.getConcreteRegisterValue(ctx.registers.rdx) # Format string
    arg4 = ctx.getConcreteRegisterValue(ctx.registers.rcx) # tm struct

    # Assuming format and tm as untainted for this simplified example
    # Normally, you would check if they are tainted similar to memcpy example

    # Call the original libc strftime to get the right output
    buffer = ctypes.create_string_buffer(arg2)
    format_str = ctx.getConcreteMemoryAreaValue(arg3, 100)  # assuming 100 is enough for format
    tm = ctx.getConcreteMemoryAreaValue(arg4, ctypes.sizeof(time.struct_time))  # Load the struct tm
    
    # Convert tm from a byte array to a struct_time object
    _tm = time.struct_time(struct.unpack("9I", bytes(tm)))
    
    # Perform strftime
    bytes_written = time.strftime(buffer, arg2, format_str.decode(), _tm)

    # Copy the result from the real strftime to Triton's memory
    for index in range(bytes_written):
        ctx.setConcreteMemoryValue(arg1 + index, buffer[index])

    # Return the number of bytes written
    return bytes_written, ctx
def __abort(ctx, tainted_flag, ast):
    print("Aborted Func Called!!!!!!!!!!!!!!!!!!!!")
    exit()
customRelocation = [
    ['strftime',          __ignore_func,           None],
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
    ['gst_buffer_map',  __ignore_func,          None],
    ['gst_pad_push',     __ignore_func,         None],
    ['g_free',            __ignore_func,        None],
    ['free',            __ignore_func,          None],
    ['g_malloc',            __ignore_func,      None],
    ['gst_adapter_available',  __ignore_func,   None],
    ['send',            __send,                 None],
    ['__stack_chk_fail', __stack_chk_fail,      None],
    ['strtol',          __strtol,               None],
    ['setvbuf',          __setvbuf,             None],
    ['alarm',           __alarm,                None],
    ['atoi',            __atoi,                 None],
    ['strcmp',          __strcmp,               None],
    ['poll',          __poll,                   None],
    ['clock_gettime',     __clock_gettime,      None],
    ['recv',            __recv,                 None],
    ['realloc',         __realloc,              None],
    ['memset',         __memset,                None],
    ['jbg_dec_free',   __ignore_func,           None],
    ['putc',           __putc,                  None],
    ['fwrite',         __fwrite,                None],
    ['fprintf',        __fprintf,               None],
    ['vfprintf',        __vfprintf,             None],
    ['close',          __ignore_func,           None],
    ['bsearch',       __bsearch,                None],
    ['exp',           __exp,                    None],
    ['access', __access ,None],
    ['isalpha', __isalpha ,None],
    ['floor', __floor ,None],
    ['memmove', __memmove ,None],
    ['toupper', __toupper ,None],
    ['mkdir', __mkdir ,None],
    ['strtok', __strtok ,None],
    ['getcwd', __getcwd ,None],
    ['pow', __pow ,None],
    ['localtime', __localtime ,None],
    ['memrchr', __memrchr ,None],
    ['islower', __islower ,None],
    ['strtoll', __strtoll ,None],
    ['strncat', __strncat ,None],

    ['abort', __abort, None],


    ['_ZSt16__ostream_insertIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_PKS3_l', __ignore_func,    None],
    ['_ZNSt15basic_streambufIcSt11char_traitsIcEE9pbackfailEi', __ignore_func,    None],
    ['_ZSt24__throw_out_of_range_fmtPKcz', __ignore_func,    None],
    ['XML_SetUserData', __ignore_func,    None],
    ['XML_ParserFree', __ignore_func,    None],
    ['_ZSt17__throw_bad_allocv', __ignore_func,    None],
    ['_ZStlsIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_St13_Setprecision', __ignore_func,    None],
    ['_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE7compareERKS4_', __ignore_func,    None],
    ['_ZNSt8__detail15_List_node_base4swapERS0_S1_',__ignore_func, None],
    ['dlerror',__ignore_func, None],
    ['getsockname',__ignore_func, None],
    ['feof',__ignore_func, None],
    ['epoll_ctl',__ignore_func, None],
    ['__cxa_begin_catch',__ignore_func, None],
    ['fdopen',__ignore_func, None],
    ['pclose',__ignore_func, None],
    ['select',__ignore_func, None],
    ['__isoc99_sscanf',__ignore_func, None],
    ['_ZNSt15basic_streambufIcSt11char_traitsIcEE6xsgetnEPcl',__ignore_func, None],
    ['_ZNSt15basic_streambufIcSt11char_traitsIcEEC2Ev',__ignore_func, None],
    ['_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE5c_strEv',__ignore_func, None],
    ['XML_ParserCreateNS',__ignore_func, None],
    ['_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEC1ERKS4_',__ignore_func, None],
    ['_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEpLEPKc',__ignore_func, None],
    ['mallopt',__ignore_func, None],
    ['ioctl',__ignore_func, None],
    ['__ctype_b_loc',__ignore_func, None],
    ['setsockopt',__ignore_func, None],
    ['fcntl',__ignore_func, None],
    ['_ZNSt9basic_iosIcSt11char_traitsIcEE4fillEc',__ignore_func, None],
    ['__assert_fail',__ignore_func, None],
    ['_ZNSt15basic_streambufIcSt11char_traitsIcEE5pbumpEi',__ignore_func, None],
    ['recvmsg',__ignore_func, None],
    ['pthread_attr_init',__ignore_func, None],
    ['_ZNKSt15basic_streambufIcSt11char_traitsIcEE5pbaseEv',__ignore_func, None],
    ['_ZNSt15basic_streambufIcSt11char_traitsIcEE5imbueERKSt6locale',__ignore_func, None],
['pwrite',__ignore_func, None],
['inet_ntop',__ignore_func, None],
['_ZNKSt13runtime_error4whatEv',__ignore_func, None],
['_ZNSt8__detail15_List_node_base7_M_hookEPS0_',__ignore_func, None],
['unlink',__ignore_func, None],
['pthread_mutex_unlock',__ignore_func, None],
['_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE4dataEv',__ignore_func, None],
['gmtime',__ignore_func, None],
['_ZNSolsEb',__ignore_func, None],
['_ZNSoD2Ev',__ignore_func, None],
['recvfrom',__ignore_func, None],
['_ZNSt13runtime_errorC1ERKNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEE',__ignore_func, None],
['openlog',__ignore_func, None],
['geteuid',__ignore_func, None],
['pthread_mutex_lock',__ignore_func, None],
['argz_stringify',__ignore_func, None],
['lseek',__ignore_func, None],
['shm_open',__ignore_func, None],
['isgraph',__ignore_func, None],
['perror',__ignore_func, None],
['_ZStlsIcSt11char_traitsIcESaIcEERSt13basic_ostreamIT_T0_ES7_RKNSt7__cxx1112basic_stringIS4_S5_T1_EE',__ignore_func, None],
['_ZNSolsEi',__ignore_func, None],
['_ZNSolsEt',__ignore_func, None],
['sscanf',__ignore_func, None],
['sched_getaffinity',__ignore_func, None],
['dlclose',__ignore_func, None],
['__cxa_bad_cast',__ignore_func, None],
['regcomp',__ignore_func, None],
['_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEC1Ev',__ignore_func, None],
['__cxa_guard_acquire',__ignore_func, None],
['_ZSt17current_exceptionv',__ignore_func, None],
['msgrcv',__ignore_func, None],
['_ZdaPv',__ignore_func, None],
['connect',__ignore_func, None],
['_ZNSolsEl',__ignore_func, None],
['pthread_mutex_init',__ignore_func, None],
['__cxa_allocate_exception',__ignore_func, None],
['_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEEaSEPKc',__ignore_func, None],
['chroot',__ignore_func, None],
['__cxa_guard_abort',__ignore_func, None],
['pthread_cond_init',__ignore_func, None],
['fclose',__ignore_func, None],
['_ZNSt13runtime_errorD2Ev',__ignore_func, None],
['memchr',__ignore_func, None],
['setsid',__ignore_func, None],
['XML_Parse',__ignore_func, None],
['regfree',__ignore_func, None],
['XML_UseParserAsHandlerArg',__ignore_func, None],
['isalnum',__ignore_func, None],
['open',__ignore_func, None],
['socket',__ignore_func, None],
['_Znam',__ignore_func, None],
['XML_GetSpecifiedAttributeCount',__ignore_func, None],
['epoll_create',__ignore_func, None],
['strstr',__ignore_func, None],
['_ZSt18_Rb_tree_decrementPSt18_Rb_tree_node_base',__ignore_func, None],
['aio_write',__ignore_func, None],
['_ZNSo5writeEPKcl',__ignore_func, None],
['_ZNSo5flushEv',__ignore_func, None],
['gettimeofday',__ignore_func, None],
['fflush',__ignore_func, None],
['_ZNSt8__detail15_List_node_base11_M_transferEPS0_S1_',__ignore_func, None],
['snprintf',__ignore_func, None],
['_ZNSolsEs',__ignore_func, None],
['_ZStlsIcSt11char_traitsIcEERSt13basic_ostreamIT_T0_ES6_St5_Setw',__ignore_func, None],
['_ZNSt15basic_streambufIcSt11char_traitsIcEED2Ev',__ignore_func, None],
['pthread_cond_wait',__ignore_func, None],
['strchr',__ignore_func, None],
['fread',__ignore_func, None],
['setgroups',__ignore_func, None],
['setresuid',__ignore_func, None],
['_ZNSt15basic_streambufIcSt11char_traitsIcEE7seekoffElSt12_Ios_SeekdirSt13_Ios_Openmode',__ignore_func, None],
['strspn',__ignore_func, None],
['closedir',__ignore_func, None],
['__cxa_guard_release',__ignore_func, None],
['initgroups',__ignore_func, None],
['_ZNKSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEE6lengthEv',__ignore_func, None],
['_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_PKc',__ignore_func, None],
['strpbrk',__ignore_func, None],
['_ZNSt15basic_streambufIcSt11char_traitsIcEE7seekposESt4fposI11__mbstate_tESt13_Ios_Openmode',__ignore_func, None],
['argz_next',__ignore_func, None],
['opendir',__ignore_func, None],
['getgrnam',__ignore_func, None],
['__gxx_personality_v0',__ignore_func, None],
['sendmsg',__ignore_func, None],
['epoll_wait',__ignore_func, None],
['_ZNSolsEPKv',__ignore_func, None],
['munmap',__ignore_func, None],
['pthread_attr_setschedparam',__ignore_func, None],
['_ZSt20__throw_length_errorPKc',__ignore_func, None],
['fchmod',__ignore_func, None],
['__cxa_throw',__ignore_func, None],
['shmget',__ignore_func, None],
['log',__ignore_func, None],
['fgets',__ignore_func, None],
['_Unwind_Resume',__ignore_func, None],
['_ZNSt8ios_base4InitD1Ev',__ignore_func, None],
['_ZStlsISt11char_traitsIcEERSt13basic_ostreamIcT_ES5_c',__ignore_func, None],
['__cxa_call_unexpected',__ignore_func, None],
['exit',__ignore_func, None],
['freeaddrinfo',__ignore_func, None],
['_ZNSt9basic_iosIcSt11char_traitsIcEE5rdbufEPSt15basic_streambufIcS1_E',__ignore_func, None],
['_ZNSt15basic_streambufIcSt11char_traitsIcEE9showmanycEv',__ignore_func, None],
['vsnprintf',__ignore_func, None],
['argz_create_sep',__ignore_func, None],
['XML_GetErrorCode',__ignore_func, None],
['pthread_self',__ignore_func, None],
['sched_setaffinity',__ignore_func, None],
['htons',__ignore_func, None],
['htonl',__ignore_func, None],
['pthread_create',__ignore_func, None],
['XML_GetCurrentLineNumber',__ignore_func, None],
['mkstemp',__ignore_func, None],
['getpwnam',__ignore_func, None],
['pthread_cond_signal',__ignore_func, None],
['getservbyname',__ignore_func, None],
['qsort',__ignore_func, None],
['_ZNSolsEb',__ignore_func, None],
['_ZNSolsEi',__ignore_func, None],
['_ZNSolsEt',__ignore_func, None],
['_ZNSolsEl',__ignore_func, None],
['_ZNSolsEs',__ignore_func, None],
['_ZNSolsEPKv',__ignore_func, None],
['_ZNSolsEj',__ignore_func, None],
['_ZNSolsEd',__ignore_func, None],
['_ZNSolsEPFRSoS_E',__ignore_func, None],
['_ZNSolsEf',__ignore_func, None],
['_ZNSolsEm',__ignore_func, None],
['_ZNSolsEPFRSt8ios_baseS0_E',__ignore_func, None],
['_ZNSt7__cxx1119basic_ostringstreamIcSt11char_traitsIcESaIcEE3strERKNS_12basic_stringIcS2_S3_EE',__ignore_func, None],
['_ZNSt7__cxx1112basic_stringIcSt11char_traitsIcESaIcEED1Ev',__ignore_func, None],
['_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate',__ignore_func, None],
['_ZNKSt7__cxx1119basic_ostringstreamIcSt11char_traitsIcESaIcEE3strEv',__ignore_func, None],
['_ZNSt7__cxx1119basic_ostringstreamIcSt11char_traitsIcESaIcEEC1ESt13_Ios_Openmode',__ignore_func, None],

['_ZNSt7__cxx1119basic_ostringstreamIcSt11char_traitsIcESaIcEED1Ev',__ignore_func, None],
['_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate',__ignore_func, None],
['_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate',__ignore_func, None],
['_ZNSt9basic_iosIcSt11char_traitsIcEE5clearESt12_Ios_Iostate',__ignore_func, None],

]