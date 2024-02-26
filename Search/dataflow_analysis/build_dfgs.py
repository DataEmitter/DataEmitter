from triton import *
from bingraphvis import *
from bingraphvis.angr import *
from bingraphvis.angr.x86 import *
from networkx import DiGraph
from contextlib import redirect_stdout
import archinfo
import io
import pyvex
import re
from pwn import *
context.log_level = 'info'

jmp_code=['jnz','jz','jnc','jc','jo','je','jne','jcxz','jecxz','jrcxz','ja','jnbe','jae','jnb','jg','jnle','jge','jnl','jl','jmp','jbe','ret','cmp']

def plot_dfg(dfg, fname, format="png"):
    '''
    将dfg以图片形式输出,默认为png
    '''
    vis = AngrVisFactory().default_common_graph_pipeline(type=True)
    vis.set_output(DotOutput(fname, format=format))
    vis.process(dfg)

def spilt_and_gather_opcodes(target_block,source_addr,target_addr,target_count,ctx,gap = 99):
    opcodes_list = []
    gap_source_addrs = []
    gap_target_addrs = []

    opcodes = b''
    collect_opcode_flag = 0
    end_flag = 0 # 跳出循环的标志
    count = 0 # 记录target_adr出现的次数
    current_num = 0 # 记录当前收集的opcodes对应的指令数量

    for (adr,opcode,inst,hooking_flag) in target_block:
        if hooking_flag:
            opcode = asm("add rsp, 0x08", arch = 'amd64')
        elif inst.isBranch():
            continue
        elif 'call' in str(inst):
            opcode = asm("sub rsp, 0x08", arch = 'amd64')
        elif 'retf' in str(inst):
            opcode = asm("add rsp, 0x10", arch = 'amd64')
            # continue
        elif 'ret' in str(inst):
            opcode = asm("add rsp, 0x08", arch = 'amd64')
        elif 'cmp' in str(inst):
            continue
        if adr==source_addr:
            opcodes+=opcode
            current_num += 1
            collect_opcode_flag=1

        elif collect_opcode_flag and adr==target_addr:
            opcodes+=opcode
            current_num += 1
            count+=1
            if count==target_count:
                end_flag = 1

        elif collect_opcode_flag:
            opcodes+=opcode
            current_num += 1

        # 划分opcodes,刷新target_statements_len，target_location_in_statement，source_statements_len
        if (current_num % gap) == 0 and current_num!=0:
            opcodes_list.append(opcodes)
            gap_target_addrs.append(adr)
            gap_source_addrs.append(gap_source_addr)
            opcodes = b''
            current_num = 0
        elif (current_num % gap) == 1:
            gap_source_addr = adr

        # 遍历结束，返回结果
        if end_flag:
            # 将最后一块opcodes收集起来
            if current_num < gap:
                opcodes_list.append(opcodes)
                gap_target_addrs.append(target_addr)
                gap_source_addrs.append(gap_source_addr)
            return opcodes_list,gap_source_addrs,gap_target_addrs

def replace_regname_with_offset(pp_list):

    for i in range(len(pp_list)):
        vex_ir_str = pp_list[i]
        if 'GET' in vex_ir_str or 'PUT' in vex_ir_str:
            pattern = r'\((\w+)\)'
            matchs = re.search(pattern,vex_ir_str)
            reg_str = matchs.group(1)
            if 't' in reg_str: # 当vex ir是'if (t517) { PUT(rip) = 0x40120d; Ijk_SigFPE_IntDiv }'
                continue
            stmt_offset = archinfo.ArchAMD64().registers[reg_str][0]
            new_vex_ir_str = vex_ir_str.replace(reg_str,'offset=%d'%(stmt_offset))
            pp_list[i] = new_vex_ir_str

    return pp_list

class DataFlowGraph():
    def __init__(self) -> None:
        self.dfgs={} # 该结构用来记录分区间后各个source到target对应的dfg
        self.gap_addrs={} # 数据流分析对应的分阶段dfg的起点和终点
        self.irsb_list = {} # 数据流图中对应的VEX IR缓存序列

    # 每一次路径探索时重置
    def fresh(self):
        self.dfgs={} # 该结构用来记录分区间后各个source到target对应的dfg
        self.gap_addrs={} # 数据流分析对应的分阶段dfg的起点和终点
        self.irsb_list = {} # 数据流图中对应的VEX IR缓存序列

    def constructDFGs(self,target_block,source_addr,target_addr,target_count,ctx):
        opcodes_list,gap_source_addrs,gap_target_addrs = spilt_and_gather_opcodes(target_block,source_addr,target_addr,target_count,ctx)
        if source_addr not in self.gap_addrs.keys():
            self.gap_addrs[source_addr] = {}
        if target_addr not in self.gap_addrs[source_addr].keys():
            self.gap_addrs[source_addr][target_addr] = {}
        self.gap_addrs[source_addr][target_addr] = (gap_source_addrs,gap_target_addrs)
        for i in range(len(opcodes_list)):    
            self.constructDFG(opcodes_list[i], gap_source_addrs[i], gap_target_addrs[i])
        
    def constructDFG(self, opcodes, source_addr, target_addr, flag=False):
        # 依据opcodes构建对应的VEX IR序列
        irsb = pyvex.lift(opcodes, source_addr, archinfo.ArchAMD64(),opt_level=0)
        irsb.pp()
        # 记录VEX IR的执行缓存序列
        buffer = io.StringIO()
        with redirect_stdout(buffer):
            irsb.pp()
        pp_list = buffer.getvalue().splitlines()[3:]
        new_pp_list = []
        for i in range(len(pp_list)):
            tmp_stmt = pp_list[i]
            if 'IMark' in tmp_stmt:
                continue
            if 'NEXT' in tmp_stmt:
                break
            pattern = r'\d+ \| (.+)'
            match = re.search(pattern,tmp_stmt)
            new_pp_list.append(match.group(1))
        if source_addr not in self.irsb_list.keys():
            self.irsb_list[source_addr]={}

        new_pp_list = replace_regname_with_offset(new_pp_list)

        self.irsb_list[source_addr][target_addr] = new_pp_list

        if irsb is not None:
            tmpsnodes = {}
            storesnodes = {}
            putsnodes = {}
            statements = irsb.statements
            dfg = DiGraph()
            for stmt_idx, stmt in enumerate(statements): 

                exprs = list(stmt.expressions) 
                stmt_node = stmt 
                dfg.add_node(stmt)
                if stmt.tag == 'Ist_WrTmp': 
                    tmpsnodes[stmt.tmp] = stmt_node 
                    if exprs[0].tag == 'Iex_Binop': # 二元操作
                        if exprs[1].tag == 'Iex_RdTmp': # 读tmp值操作
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[1], stmt_node)
                        if exprs[2].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[2].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[2], stmt_node)

                    elif exprs[0].tag == 'Iex_Unop': # 一元操作
                        if exprs[1].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[1], stmt_node)

                    elif exprs[0].tag == 'Iex_RdTmp': # 读取临时变量的值
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                    elif exprs[0].tag == 'Iex_Get': # 获取寄存器的值
                        if exprs[0].offset in putsnodes:
                            dfg.add_edge(putsnodes[exprs[0].offset], stmt_node)
                        if len(exprs) > 1 and exprs[1].tag == "Iex_RdTmp":
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        elif len(exprs) > 1:
                            dfg.add_edge(exprs[1], stmt_node)

                    elif exprs[0].tag == 'Iex_Load': # 内存中加载数据
                        if exprs[1].tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                        else:
                            dfg.add_edge(exprs[1], stmt_node)

                    else:
                        for e in exprs[1:]:
                            if e.tag == 'Iex_RdTmp':
                                dfg.add_edge(tmpsnodes[e.tmp], stmt_node)
                            else:
                                dfg.add_edge(e, stmt_node)

                elif stmt.tag == 'Ist_Store':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                    elif exprs[0].tag == 'Iex_Const':
                        dfg.add_edge(exprs[0], stmt_node)

                    if exprs[1].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                    else:
                        dfg.add_edge(exprs[1], stmt_node)

                elif stmt.tag == 'Ist_Put':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)
                    elif exprs[0].tag == 'Iex_Const':
                        dfg.add_edge(exprs[0], stmt_node)
                    putsnodes[stmt.offset] = stmt_node

                elif stmt.tag == 'Ist_Exit':
                    if exprs[0].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                elif stmt.tag == 'Ist_Dirty':
                    tmpsnodes[stmt.tmp] = stmt_node
                elif stmt.tag == 'Ist_CAS':
                    tmpsnodes[stmt.oldLo] = stmt_node
                else:
                    for e in stmt.expressions:
                        if e.tag == 'Iex_RdTmp':
                            dfg.add_edge(tmpsnodes[e.tmp], stmt_node)
                        else:
                            dfg.add_edge(e, stmt_node)

            for vtx in list(dfg.nodes()):
                if dfg.degree(vtx) == 0:
                    dfg.remove_node(vtx)

            if dfg.size() > 0:
                if source_addr not in self.dfgs.keys():
                    self.dfgs[source_addr]={}
                self.dfgs[source_addr][target_addr] = dfg
        if flag:
            plot_dfg(dfg, "dfg_0x%x_0x%x"%(source_addr,target_addr), format="png") 
