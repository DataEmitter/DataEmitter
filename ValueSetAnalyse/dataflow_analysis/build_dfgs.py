from triton import *
from bingraphvis import *
from bingraphvis.angr import *
from bingraphvis.angr.x86 import *
from networkx import DiGraph
from contextlib import redirect_stdout
from config.config import *
import archinfo
import io
import pyvex
import re
import time
import threading
import os
from pwn import asm

jmp_code=['jnz','jz','jnc','jc','jo','je','jne','jcxz','jecxz','jrcxz','ja','jnbe','jae','jnb','jg','jnle','jge','jnl','jl','jmp','jbe','ret','cmp']

def plot_dfg(dfg, fname, format="png"):
    vis = AngrVisFactory().default_common_graph_pipeline(type=True)
    vis.set_output(DotOutput(fname, format=format))
    vis.process(dfg)

def handle_rep_ins(rep_num,inst):
    if "repne scasb al, byte ptr es:[edi]" in str(inst):
        opcode1 = asm("add edi, %d"%(rep_num), arch = 'i386')
        opcode2 = asm("sub ecx, %d"%(rep_num), arch = 'i386')
        opcode = opcode1 + opcode2
    return opcode

def handle_opcode(opcode, inst, hooking_flag):
    num = 1
    if hooking_flag:
        if ANALYSE_MODE == "X64":
            opcode = asm("add rsp, 0x08", arch = 'amd64')
        else:
            opcode = asm("add esp, 0x04", arch = 'i386')
    
    elif inst.isBranch():
        opcode = None
    elif 'setne' in str(inst):
        opcode = None
    elif 'call' in str(inst):
        if ANALYSE_MODE == "X64":
            opcode = asm("sub rsp, 0x08", arch = 'amd64')
        else:
            opcode = asm("sub esp, 0x04", arch = 'i386')
    elif 'retf' in str(inst):
        if ANALYSE_MODE == "X64":
            opcode = asm("add rsp, 0x10", arch = 'amd64')
        else:
            opcode = asm("add esp, 0x08", arch = 'i386')
    elif 'ret' in str(inst):
        if ANALYSE_MODE == "X64":
            opcode = asm("add rsp, 0x08", arch = 'amd64')
        else:
            opcode = asm("add esp, 0x04", arch = 'i386')
    elif 'rep' in str(inst):
        
        if "repne scasb al, byte ptr es:[edi]" in str(inst):
            opcode1 = asm("add edi, 1", arch = 'i386')
            opcode2 = asm("sub ecx, 1", arch = 'i386')
            opcode = opcode1 + opcode2
            num = 2
        
        elif "rep stosd dword ptr es:[edi], eax" in str(inst):
            opcode1 = asm("add edi, ecx", arch = 'i386')
            opcode2 = asm("add edi, ecx", arch = 'i386')
            opcode3 = asm("add edi, ecx", arch = 'i386')
            opcode4 = asm("add edi, ecx", arch = 'i386')
            opcode = opcode1 + opcode2 + opcode3 + opcode4
            num = 4
    return opcode, num

def write_inst_file(ins_list, source_adr, target_adr, handled_flag):
    if handled_flag:
        directory = "test/{}/handled_instruction_result".format(binary_name)
        os.makedirs(directory, exist_ok=True)
    else:
        directory = "test/{}/instruction_result".format(binary_name)
        os.makedirs(directory, exist_ok=True)
    filename = "0x{:x}_0x{:x}.txt".format(source_adr, target_adr)
    ins_filepath = os.path.join(directory, filename)
    with open(ins_filepath, "w") as f:
        for inst in ins_list:
            f.write(str(inst)+'\n')

def spilt_and_gather_opcodes(target_block,source_addr,target_addr,target_count,gap = 98):
    opcodes_list = []
    gap_source_addrs = []
    gap_target_addrs = []
    cmp_list = []
    ins_list = [] 
    handled_ins_list = []
    cur_ins_list = []
    cur_handled_ins_list = []

    opcodes = b''
    collect_opcode_flag = 0
    end_flag = 0 
    end_cur_flag = 0 
    count = 0 
    dfg_num = 0 
    current_num = 0 

    directory = "test/{}/handled_instruction_result".format(binary_name)
    os.makedirs(directory, exist_ok=True)
    filename = "0x{:x}_0x{:x}.txt".format(source_addr, target_addr)
    handled_ins_filepath = os.path.join(directory, filename)
    with open(handled_ins_filepath, "w") as f:
        pass
    directory = "test/{}/instruction_result".format(binary_name)
    os.makedirs(directory, exist_ok=True)
    ins_filepath = os.path.join(directory, filename)
    with open(ins_filepath, "w") as f:
        pass
    
    gap_source_addr = None
    for i in range(len(target_block)):
        adr = target_block[i][0]
        opcode = target_block[i][1]
        inst = target_block[i][2]
        hooking_flag = target_block[i][3]
        
        if adr == source_addr:
            ins_list.append(str(inst))
            cur_ins_list.append(str(inst))

            opcode, num = handle_opcode(opcode, inst, hooking_flag)
            if opcode != None:
                handled_ins_list.append(str(inst))
                cur_handled_ins_list.append(str(inst))
                opcodes += opcode
                current_num += num
                collect_opcode_flag = 1
                gap_source_addr = adr 

        elif collect_opcode_flag and adr == target_addr:
            ins_list.append(str(inst))
            cur_ins_list.append(str(inst))

            opcode, num = handle_opcode(opcode, inst, hooking_flag)
            if opcode!= None:
                handled_ins_list.append(str(inst))
                cur_handled_ins_list.append(str(inst))
                opcodes += opcode
                current_num += num               
            count += 1
            if count == target_count:
                end_flag = 1

        elif collect_opcode_flag:
            ins_list.append(str(inst))
            cur_ins_list.append(str(inst))
            opcode, num = handle_opcode(opcode, inst, hooking_flag)
            if opcode != None:
                handled_ins_list.append(str(inst))
                cur_handled_ins_list.append(str(inst))
                if gap_source_addr == None:
                    gap_source_addr = adr 
                opcodes += opcode
                current_num += num
        
        else:
            continue

        if 'cmp' in str(inst) or 'test' in str(inst):
            cmp_list.append((dfg_num, current_num - 1))
        
        if (current_num % gap) == 0 and current_num != 0:
            opcodes_list.append(opcodes)
            gap_target_addrs.append(adr)
            gap_source_addrs.append(gap_source_addr)
            write_inst_file(cur_ins_list, gap_source_addr, adr, False)
            write_inst_file(cur_handled_ins_list, gap_source_addr, adr, True)
            cur_ins_list = []
            cur_handled_ins_list = []
            opcodes = b''
            current_num = 0
            dfg_num += 1
            end_cur_flag = 1
        elif (current_num % gap) == 1 and current_num != 1:
            opcodes_list.append(opcodes)
            gap_target_addrs.append(adr)
            gap_source_addrs.append(gap_source_addr)
            write_inst_file(cur_ins_list, gap_source_addr, adr, False)
            write_inst_file(cur_handled_ins_list, gap_source_addr, adr, True)
            cur_ins_list = []
            cur_handled_ins_list = []
            opcodes = b''
            current_num = 0
            dfg_num += 1
            end_cur_flag = 1
        elif end_cur_flag:
            gap_source_addr = adr
            end_cur_flag = 0
        if end_flag:
            if current_num < gap and current_num > 0:
                opcodes_list.append(opcodes)
                gap_target_addrs.append(target_addr)
                gap_source_addrs.append(gap_source_addr)
                write_inst_file(cur_ins_list, gap_source_addr, target_addr, False)
                write_inst_file(cur_handled_ins_list, gap_source_addr, target_addr, True)
            break
    write_inst_file(ins_list, source_addr, target_addr, False)
    write_inst_file(handled_ins_list, source_addr, target_addr, True)

    return opcodes_list, gap_source_addrs, gap_target_addrs, cmp_list, ins_list

def replace_regname_with_offset(pp_list):
    for i in range(len(pp_list)):
        vex_ir_str = pp_list[i]
        if 'GET' in vex_ir_str or 'PUT' in vex_ir_str:
            pattern = r'\((\w+)\)'
            matchs = re.search(pattern,vex_ir_str)
            reg_str = matchs.group(1)
            if 't' in reg_str: 
                continue
            if ANALYSE_MODE == "X64":
                stmt_offset = archinfo.ArchAMD64().registers[reg_str][0]
            else:
                stmt_offset = archinfo.ArchX86().registers[reg_str][0]
            new_vex_ir_str = vex_ir_str.replace(reg_str,'offset=%d'%(stmt_offset))
            pp_list[i] = new_vex_ir_str

    return pp_list

def get_reg_infos(stmt_str):
    pattern = r'PUT\((.*?)\)'
    match = re.search(pattern, stmt_str)
    if match:
        reg_str = match.group(1)
    else:
        exit(-1)
    arch = archinfo.ArchX86()
    register_dict = arch.registers
    for key, value in register_dict.items():
        if key == reg_str:
            return (value[0],value[1])

def update_putsnodes(putsnodes,new_offset,new_length,stmt_node):
    new_end = new_offset + new_length
    updated_putsnodes = {}
    updated_putsnodes[(new_offset,new_length)] = stmt_node
    for (offset,length) in putsnodes:
        stmt = putsnodes[(offset,length)]
        end = offset + length
        if offset >= new_end or end <= new_offset:
            updated_putsnodes[(offset,length)] = stmt
        else:
            if new_offset <= offset and new_end >= end:
                continue
            elif new_offset > offset and end > new_offset and new_end >= end:
                updated_putsnodes[(offset,new_offset-offset)] = stmt
            elif offset >= new_offset and new_end > offset and end > new_end:
                updated_putsnodes[(new_end,end-new_end)] = stmt
            elif new_offset > offset and end > new_end:
                updated_putsnodes[(offset,new_offset-offset)] = stmt
                updated_putsnodes[(new_end,end-new_end)] = stmt
    return updated_putsnodes 

def add_edge_for_Get(dfg, stmt_str, stmt_node, putsnodes):
    pattern = r'\((.*?)\)'
    match = re.search(pattern, stmt_str)
    if match:
        reg_str = match.group(1)
    else:
        exit(-1)
    arch = archinfo.ArchX86()
    register_dict = arch.registers
    for key, value in register_dict.items():
        if key == reg_str:
            offset,length = value[0],value[1]
            break
    for (tmp_offset,tmp_length) in putsnodes:
        
        if not (offset >= (tmp_offset+tmp_length) or (offset+length) <= tmp_offset):
            dfg.add_edge(putsnodes[(tmp_offset,tmp_length)], stmt_node)

def constructDFG(opcodes, source_addr, target_addr, flag=False):
    if ANALYSE_MODE == "X64":
        irsb = pyvex.lift(opcodes, source_addr, archinfo.ArchAMD64(),opt_level=0)
    else:
        irsb = pyvex.lift(opcodes, source_addr, archinfo.ArchX86(),opt_level=0)
    
    
    buffer = io.StringIO()
    with redirect_stdout(buffer):
        irsb.pp()
    pp_list = buffer.getvalue().splitlines()[3:]
    new_pp_list = []
    imark_num = 0
    for i in range(len(pp_list)):
        tmp_stmt = pp_list[i]
        if 'IMark' in tmp_stmt:
            new_pp_list.append('IMark_%d'%imark_num)
            imark_num += 1
            
        if 'NEXT' in tmp_stmt:
            break
        pattern = r'\d+ \| (.+)'
        match = re.search(pattern,tmp_stmt)
        new_pp_list.append(match.group(1))

    
    new_pp_list = replace_regname_with_offset(new_pp_list)

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
                if exprs[0].tag == 'Iex_Binop': 
                    if exprs[1].tag == 'Iex_RdTmp': 
                        dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                    else:
                        dfg.add_edge(exprs[1], stmt_node)
                    if exprs[2].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[2].tmp], stmt_node)
                    else:
                        dfg.add_edge(exprs[2], stmt_node)

                elif exprs[0].tag == 'Iex_Unop': 
                    if exprs[1].tag == 'Iex_RdTmp':
                        dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                    else:
                        dfg.add_edge(exprs[1], stmt_node)

                elif exprs[0].tag == 'Iex_RdTmp': 
                    dfg.add_edge(tmpsnodes[exprs[0].tmp], stmt_node)

                elif exprs[0].tag == 'Iex_Get': 
                    if exprs[0].offset in putsnodes:
                        
                        if exprs[0].offset % 4 == 0:
                            dfg.add_edge(putsnodes[exprs[0].offset], stmt_node)
                        else:
                            dfg.add_edge(putsnodes[exprs[0].offset-1], stmt_node)
                    if len(exprs) > 1 and exprs[1].tag == "Iex_RdTmp":
                        dfg.add_edge(tmpsnodes[exprs[1].tmp], stmt_node)
                    elif len(exprs) > 1:
                        dfg.add_edge(exprs[1], stmt_node)

                elif exprs[0].tag == 'Iex_Load': 
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
                
                
                if stmt.offset % 4 == 0:
                    putsnodes[stmt.offset] = stmt_node
                else:
                    putsnodes[stmt.offset-1] = stmt_node

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

    if flag:
        plot_dfg(dfg, "dfg/0x%x_0x%x"%(source_addr,target_addr), format="png") 
    
    return dfg,new_pp_list

class BuildDfg(threading.Thread):
    def __init__(self,opcodes, source_addr, target_addr) -> None:
        threading.Thread.__init__(self)  
        self.opcodes = opcodes
        self.source_addr = source_addr
        self.target_addr = target_addr
        self.dfg_info = [] 
        self.irsb_list_info = [] 

    def run(self):
        dfg,irsb_list = constructDFG(self.opcodes, self.source_addr, self.target_addr, flag=False)
        self.dfg_info = [self.source_addr,self.target_addr,dfg]
        self.irsb_list_info = [self.source_addr,self.target_addr,irsb_list]

    def get_result(self):
        return self.dfg_info,self.irsb_list_info

class DataFlowGraph():
    def __init__(self,plt_base_address,plt_size) -> None:
        self.dfgs={} 
        self.gap_addrs={} 
        self.irsb_list = {} 
        self.cmp_list = {} 
        self.ins_list = {} 
        self.plt_base_address = plt_base_address
        self.plt_size = plt_size

    def fresh(self):
        self.dfgs={} 
        self.gap_addrs={} 
        self.irsb_list = {} 
        self.cmp_list = {} 
        self.ins_list = {} 

    def constructDFGs(self,target_block,source_addr,target_addr,target_count,label = False):
        opcodes_list,gap_source_addrs,gap_target_addrs,cmp_list,ins_list = spilt_and_gather_opcodes(target_block,source_addr,target_addr,target_count)
        if source_addr not in self.gap_addrs.keys():
            self.gap_addrs[source_addr] = {}
        self.gap_addrs[source_addr][target_addr] = (gap_source_addrs,gap_target_addrs)
        if source_addr not in self.cmp_list.keys():
            self.cmp_list[source_addr] = {}
        self.cmp_list[source_addr][target_addr] = cmp_list
        if source_addr not in self.ins_list.keys():
            self.ins_list[source_addr] = {}
        self.ins_list[source_addr][target_addr] = ins_list

        for i in range(len(opcodes_list)):
            source_addr = gap_source_addrs[i]
            target_addr = gap_target_addrs[i]
            opcodes = opcodes_list[i]
            dfg,irsb_list = constructDFG(opcodes, source_addr, target_addr, flag=False)
            if source_addr not in self.dfgs.keys():
                self.dfgs[source_addr] = {}
            self.dfgs[source_addr][target_addr] = dfg
            if source_addr not in self.irsb_list.keys():
                self.irsb_list[source_addr] = {}
            self.irsb_list[source_addr][target_addr] = irsb_list
        
        if label:
            for i in range(len(gap_source_addrs)):
                directory = "test/{}/vexir_result".format(binary_name)
                os.makedirs(directory, exist_ok=True)
                filename = "0x{:x}_0x{:x}.txt".format(gap_source_addrs[i], gap_target_addrs[i])
                vexir_filepath = os.path.join(directory, filename)
                with open(vexir_filepath, "w") as f:
                    irsb_list = self.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]]
                    for j in range(len(irsb_list)):
                        f.write(irsb_list[j]+'\n')
                    f.write('\n\n')
