'''
    该文件用于对程序进行静态的分析
'''
import angr
import re
import config.__config as cn
from config.__config import *
import sys
import dill
from utils.tool_lib import is_op_equal
import subprocess
import re
from capstone import *
from capstone.x86 import *

def find_by_objdump(bin_path,angr_proj):
    # 执行objdump命令并获取输出
    result = subprocess.run(['objdump', '-d', bin_path], capture_output=True, text=True)
    output = result.stdout
    final_return = []

    # 遍历目标函数列表
    for gadget in Target_Gadget:
        # 在输出中搜索包含目标函数的行
        gadget_lines = re.findall(r'^\s*([0-9a-fA-F]+):\s+.*\b{}\b.*$'.format(gadget), output, flags=re.MULTILINE)

        # 提取指令地址
        gadget_instructions = [line.split(':')[0] for line in gadget_lines]

        # 打印结果
        if gadget_instructions:
            for address in gadget_instructions:
                try:
                    final_return.append(position_node(node_type=gadget, addr=int(address,16),obj=angr_proj.factory.block(int(address,16)),rank=TYPE_RANK[gadget]))
                except:
                    pass
    return final_return

class position_node():
    def __init__(self,
                 node_type,
                 addr,
                 obj, # angr中获取的对象类型：switch类型是node， loop类型是loop, gadget的类型是node
                 rank,
                 ) -> None:
        self.type = node_type
        self.addr = addr
        self.obj = obj
        self.rank = rank

def check_static_primitives(cfg, angr_proj):
    final_result = []
    for block in cfg.nodes():
        ins_stack = [] # 该结构仅仅用于存储当前 block 中的原语，跨基本块的并不会记录
        block_obj = block.block
        if block_obj is None:
            continue
        for insn in block_obj.capstone.insns:
            # print(insn)
            if len(insn.operands) == 0:
                # 这里是endber，ret这种指令，啥也不需要干
                # print("Nothing!")
                continue
            elif len(insn.operands) == 2: 
                if not insn.operands[0].access & CS_AC_WRITE:
                    continue
                if insn.operands[0].type == X86_OP_MEM and insn.operands[-1].type == X86_OP_IMM: # 这里判断
                    # mov [] , imm
                    # 这里是store一个常量指令
                    pass
                elif insn.operands[0].type == X86_OP_MEM and insn.operands[-1].type == X86_OP_REG and 'mov' in insn.mnemonic:
                    target_reg = "".join(insn.op_str.split(',')[-1].split()) 
                    ins_stack.reverse()
                    new_P = [insn]
                    for per_insn in ins_stack:
                        if len(per_insn.operands) == 0:
                            continue
                        elif len(per_insn.operands) == 1:
                            if is_op_equal(target_reg,"".join(per_insn.op_str.split()[-1].split())):
                                # inc这种指令当前要存起来
                                new_P.append(per_insn)
                        elif len(per_insn.operands) == 2 :
                            if per_insn.op_str.split(', ')[0] == per_insn.op_str.split(', ')[0] and per_insn.mnemonic == 'xor':
                                # 直接清零了就没有意义了
                                break
                            if is_op_equal(target_reg,"".join(per_insn.op_str.split(",")[0].split())):
                                new_P.append(per_insn)
                                # 这里替换下一次要追踪的寄存器
                                if per_insn.operands[-1].type == X86_OP_MEM or per_insn.operands[-1].type == X86_OP_IMM:
                                    
                                    if len(new_P) == 1:
                                        # 如果只是单条指令，则没有什么意义
                                        break
                                    final_result.append(
                                        position_node(
                                            node_type="SEQ",
                                            addr = block.addr,
                                            obj = block, # angr中获取的对象类型：switch类型是node， loop类型是loop, gadget的类型是node
                                            rank= TYPE_RANK["SEQ"],
                                        )
                                    )
                                    new_P.reverse()
                                    break
                                elif per_insn.operands[-1].type == X86_OP_REG:
                                    # 这里直接换目标进行修改了
                                    target_reg = "".join(per_insn.op_str.split(",")[-1].split())
                        elif len(per_insn.operands) == 3: # 这里如果是三操作数
                            if is_op_equal(target_reg,"".join(per_insn.op_str.split(",")[0].split())):
                                new_P.append(per_insn)

                elif insn.operands[0].type == X86_OP_REG and insn.operands[-1].type == X86_OP_IMM:
                    # 这里是对寄存器赋立即数，这个也直入栈
                    ins_stack.append(insn)
                elif insn.operands[0].type == X86_OP_REG and insn.operands[-1].type == X86_OP_REG:
                    # 这里是两个寄存器的赋值 不用管直接入栈
                    ins_stack.append(insn)
                elif insn.operands[0].type == X86_OP_REG and insn.operands[-1].type == X86_OP_MEM:
                    # 这里所有的指令都是load mov reg, [reg],load指令直接取出即可
                    ins_stack.append(insn)
                elif insn.operands[0].type == X86_OP_MEM and insn.operands[-1].type == X86_OP_MEM:
                    final_result.append(
                                        position_node(
                                            node_type="SEQ",
                                            addr = block.addr,
                                            obj = block, # angr中获取的对象类型：switch类型是node， loop类型是loop, gadget的类型是node
                                            rank= TYPE_RANK["SEQ"],
                                        )
                                    )
            elif len(insn.operands) == 1:
                if insn.operands[0].access & CS_AC_WRITE and 'pop' not in insn.mnemonic:
                    # 这里筛选出所有的inc指令
                    ins_stack.append(insn)
            else:
                if len(insn.operands) == 3:
                    ins_stack.append(insn)
                else:
                    # print("unconsiderd inst",insn)
                    pass
    print("After Got SEQ:", len(final_result))
    return final_result 
def static_extract_local_features(start_position, file_path,Current_ARCH,cfg_model = None,loop_list=None,angr_proj = None):
    if angr_proj is None:
        if Current_ARCH== 1: # 64w为分析
            angr_proj=angr.Project(file_path, arch='x86_64',auto_load_libs=False)
        else:
            angr_proj=angr.Project(file_path, arch='x86',auto_load_libs=False)

    final_return = [] 
    import lief
    binary = lief.parse(file_path)
    relocations = [x for x in binary.pltgot_relocations]
    symbol_dict = {}
    print("start Search lib funcs")
    for rel in relocations:
        symbolName = rel.symbol.name
        # print(symbolName, hex(rel.address))
        symbol_dict[rel.address] = symbolName
    if cfg_model is None:
        cfg = angr_proj.analyses.CFGFast()
    else:
        cfg = cfg_model
    switch_nodes = {}
    for node in cfg.nodes():
        if len(node.successors) > 2:
            if node.block is not None:
                switch_nodes[node.block.instruction_addrs[-1]- cn.ANGR_BASE] = node
            else:
                switch_nodes[node.addr - cn.ANGR_BASE ] = node
    final_return += find_switch_loop(angr_proj,cfg=cfg,loop_list=loop_list)
    before_len = len(final_return)
    print("Got Switch Case Node:",len(final_return))
    # 遍历 CFG 中的每个基本块
    for block in cfg.nodes():
        block_obj = block.block
        if block_obj is None:
            continue
        # 打印基本块的起始地址和指令内容
        for insn in block_obj.capstone.insns:
            # print("0x%x:\t%s\t%s" % (insn.address,insn.mnemonic, insn.op_str))
            final_return += check_libc_call(insn,
                                            first_ins = block_obj.capstone.insns[0], # 这里找第一个block的点
                                            proj=angr_proj,symbol_dict=symbol_dict, 
                                            target_func=Target_Gadget)
    print("Got libc call:",len(final_return)- before_len)
    if before_len == len(final_return):
        # 这里说明确实没有找到
        final_return += find_by_objdump(file_path,angr_proj)
    print("Got All libc call:",len(final_return))
    print("Got All Static Gadget:",len(final_return))
    return final_return,angr_proj,cfg

# 寻找程序中的循环分发结构
def find_switch_loop(angr_proj,cfg,loop_list=None):
    '''
        遍历当前程序中包含的循环结构
    '''
    return_list = []
    # 这里如果没有传进来loop_list 那就自己生成
    if loop_list is None:
        loop_list=angr_proj.analyses.LoopFinder().loops
        with open((sys.argv[1]).split('/')[-1]+'.loop_list', 'wb') as f:
            dill.dump(loop_list, f)
    for  per_loop  in loop_list:
        '''
            在循环结构中进行搜索，找到有价值的循环的入口点
        '''
        for per_node in per_loop.body_nodes:
            try:
                if len(per_node.successors()) > 2:
                    return_list.append(position_node('switch',per_node.addr,per_node,rank=TYPE_RANK['switch']))
            except:
                cfg_node = cfg.get_any_node(per_node.addr)
                if len(cfg_node.successors) > 2:
                    return_list.append(position_node('switch',per_node.addr,per_node,rank=TYPE_RANK['switch']))
    return return_list

def check_libc_call(insn, first_ins, proj,symbol_dict, target_func:str=None):

    final_return = []
    if insn.mnemonic == 'call':
        # 获取调用目标
        target = insn.op_str
        # check call [rip + addr] 就不可能是libc的call
        if '+' in target:
            return []
        # check call rax
        try:
            tmp_block = proj.factory.block(int(target,16))
        except:
            print("[-] Not Valid Jmp Target -->",target)
            return [] # 这里没什么可以加的，就继续
        
        
        if len(tmp_block.capstone.insns) <2: # 结点中只有一个条指令的基本上就可以认为是libc call
            for p_ins in tmp_block.capstone.insns:
                # print("Double Find --> 0x%x:\t%s\t%s" % (p_ins.address,p_ins.mnemonic, p_ins.op_str))
                if p_ins.mnemonic == 'jmp':
                    p_target = p_ins.op_str
                    tmp = re.findall(r'\[(.*)\]',p_target)
                    if len(tmp) == 0:
                        continue
                    else:
                        if  '+' in tmp[0]: # 这里说明格式
                            if IS_LIB: #  这里的存在二进制程序和库函数之间的区别
                                target_address = int(tmp[0].split('+')[-1],16)+p_ins.address+0x6 - cn.ANGR_BASE # 减去程序镜像基址
                            else:
                                target_address = int(tmp[0].split('+')[-1],16)
                        else:
                            target_address = int(tmp[0],16)+p_ins.address+0x6 # ?????
                        # print('libc_store',hex(target_address))
                        if target_address in symbol_dict:
                            # print("Catch Libc Call:",symbol_dict[target_address])
                            if target_func is not None:
                                if symbol_dict[target_address] in target_func:
                                    # 找到目标函数的调用位置所在的基本块进行记录
                                    # 这里是记录调用块而不是call的本身
                                    final_return.append(position_node(symbol_dict[target_address],first_ins.address,proj.factory.block(first_ins.address),rank=TYPE_RANK[symbol_dict[target_address]]))

    return final_return