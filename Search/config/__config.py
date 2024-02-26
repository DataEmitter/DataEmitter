'''
    该文件用于存储运行时所需要的所有配置
'''
from copy import deepcopy
IS_LIB = True# <--------------------------
# 选择分析模块
X86_64 = 1
X86_32 = 0
SEARCH_DEPTH = 18
FORCERUN = True # 没有探索路径数量限制
# 选择分析的是二进制程序还是动态链接库
BIN = 0 # 如果是1表示分析的是可执行文件
# 分析框架
ANALYSE_MODE = X86_64 #  <------------------------
MAX_INST_TIMES = 2000 # 最大指令执行条数
MAX_ACT_INST_TIME = 400 # 最大分支处理数
if ANALYSE_MODE is X86_64:
    NOW_ARCH = 4
else:
    NOW_ARCH =3
DEBUG = True
HARD_DEBUG = False
target_address = None
target_value = None
if ANALYSE_MODE is X86_32:
    ANGR_BASE = 0x8048000
else:
    ANGR_BASE =  0x400000
DEBUG_ADDR = {
}
# 这里设置好预先要查找的libc_gadget
Target_Gadget = [
    'memcpy',
    'strcpy',
    'strncpy',
    'strncat',
    'printf',
    'vsnprintf',
    'recv',
    'memmove',
    'memmove',
    'memcpy_chk',
    'execl',
    'sudo_memset_s',
    ]

# 为当前程序中的类型附权重
TYPE_RANK = {
    'memcpy': 10,
    'strcpy': 1,
    'strncpy': 1,
    'vsnprintf': 1,
    'assemble': 2,
    'switch':12,
    'vsnprintf':1,
    'recv':10,
    'memmove':5,
    'memmove':5,
    'SEQ':10,
    'strncat':2,
    'printf':1,
    'execl':10,
    'sudo_memset_s':1,
}
# 标记污染内存
'''
    这里设置两种形式的污染内存
    寄存器： size  --> 取寄存器内容为地址向后进行污染操作
    内存地址： size
'''
REG_BASED_TAINT = {
    # 'eax':0x1148
}
# 标记受污染的寄存器
TAINTED_REG = [
    # 'rax' # ffmpeg
]
TAINTED_MEM = {
    0x7fffd0025960: 0x200,
    0x7fffd00231b0: 0x2
    }
# 最大输入值
MAX_INPUT_LEN = 50
# 如果需要程序输入时，std_input为空，则如何处理当前程序
RANDOM_INPUT = True
word_list=[
    '5',
    '\n',
    '1',
    '2',
    '3',
    '4',
    '6',
]
# 程序运行中所需要的输入，按照每行一个
std_input = [
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
    '5','\n',
]
# 构造一个列表副本
back_std_input = deepcopy(std_input)
std_file_input = [
    # '文件内容/行'
    'FILE INPUT LINE'
]

# Gadget结果存放位置
Gadget_save_path = './result/gstreamer.gadget'
# dispatcher结果存放位置
dispatcher_save_path = './result/gstreamer.dispatcher'
ign_gadget_path = './result/gstreamer.act'

'''
    非设置部分用于对上述内容进行数据的处理
'''
std_input.reverse()
std_file_input.reverse()