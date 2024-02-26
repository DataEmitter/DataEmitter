import z3
import re
import io
from . import generate_z3_exprs
from config.config import *
from contextlib import redirect_stdout


def find_conditional_jumps(target_block,source_addr,target_addr,target_count):
    conditional_jumps = []
    flag = False 
    counts = 0 
    
    for i in range(len(target_block)):
        
        if source_addr == target_block[i][0] or flag:
            flag = True
        if flag:
            instruction = target_block[i][2]
            if 'cmp' in str(instruction) or "test" in str(instruction):
                cmp_code = str(instruction).split(' ')[1]
                
                for j in range(i+1, len(target_block)):
                    next_instruction = target_block[j][2]
                    if next_instruction.isBranch():
                        jmp_code = str(next_instruction).split(' ')[1]
                        jmp_flag = next_instruction.isConditionTaken()
                        conditional_jumps.append((cmp_code,jmp_code,jmp_flag))
                        break
        if target_addr == target_block[i][0]:
            counts += 1
            if counts == target_count:
                flag = False
    return conditional_jumps

def get_operands_by_cmp_list(cmp_list,irsb_lists):
    operands_list = []
    pattern = '(\d+)\((.*?),(.*?)\)'
    for i in range(len(cmp_list)):
        dfg_pos = cmp_list[i][0]
        ins_pos = cmp_list[i][1]
        irsb_list = irsb_lists[dfg_pos]
        for j in range(len(irsb_list)):
            if irsb_list[j] == 'IMark_%d'%ins_pos:
                for m in range(j+1,len(irsb_list)):
                    if 'Sub' in irsb_list[m] or 'And' in irsb_list[m]:
                        match = re.search(pattern,irsb_list[m])
                        size = match.group(1)
                        tmp1 = match.group(2) 
                        tmp2 = match.group(3)
                        break
                    else:
                        continue
                operands_list.append((tmp1,tmp2,size,dfg_pos))
                break
    return operands_list

def get_conditions_from_control_flow(conditional_jumps,operands_exprs_list,All_infos,source_dctx):
    
    all_conditions = []
    for i in range(len(conditional_jumps)):
        tmp1_expr = operands_exprs_list[i][0]
        tmp2_expr = operands_exprs_list[i][1]
        conditions1 = generate_z3_exprs.get_conditions_in_z3_expr(tmp1_expr,All_infos,source_dctx)
        conditions2 = generate_z3_exprs.get_conditions_in_z3_expr(tmp2_expr,All_infos,source_dctx)
        all_conditions.extend(conditions1)
        all_conditions.extend(conditions2)

        cmp_code = conditional_jumps[i][0]
        if cmp_code == 'cmp':
            jmp_code = conditional_jumps[i][1]
            jmp_flag = conditional_jumps[i][2]
            if jmp_code == 'je':
                if jmp_flag:
                    all_conditions.append(tmp1_expr == tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr != tmp2_expr)
            elif jmp_code == 'jne':
                if jmp_flag:
                    all_conditions.append(tmp1_expr != tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr == tmp2_expr)
            elif jmp_code == 'jl':
                if jmp_flag:
                    all_conditions.append(tmp1_expr < tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr >= tmp2_expr)
            elif jmp_code == 'jle':
                if jmp_flag:
                    all_conditions.append(tmp1_expr <= tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr > tmp2_expr)
            elif jmp_code == 'jg':
                if jmp_flag:
                    all_conditions.append(tmp1_expr > tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr <= tmp2_expr)
            elif jmp_code == 'jge':
                if jmp_flag:
                    all_conditions.append(tmp1_expr >= tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr < tmp2_expr)
            elif jmp_code == 'ja':
                if jmp_flag:
                    all_conditions.append(z3.UGT(tmp1_expr, tmp2_expr))
                else:
                    all_conditions.append(z3.ULE(tmp1_expr, tmp2_expr))
            elif jmp_code == 'jae':
                if jmp_flag:
                    all_conditions.append(z3.UGE(tmp1_expr, tmp2_expr))
                else:
                    all_conditions.append(z3.ULT(tmp1_expr, tmp2_expr))
            elif jmp_code == 'jb':
                if jmp_flag:
                    all_conditions.append(z3.ULT(tmp1_expr, tmp2_expr))
                else:
                    all_conditions.append(z3.UGE(tmp1_expr, tmp2_expr))
            elif jmp_code == 'jbe':
                if jmp_flag:
                    all_conditions.append(z3.ULE(tmp1_expr, tmp2_expr))
                else:
                    all_conditions.append(z3.UGT(tmp1_expr, tmp2_expr))
            elif jmp_code == 'js':
                if jmp_flag:
                    all_conditions.append(tmp1_expr < tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr >= tmp2_expr)
            elif jmp_code == 'jns':
                if jmp_flag:
                    all_conditions.append(tmp1_expr >= tmp2_expr)
                else:
                    all_conditions.append(tmp1_expr < tmp2_expr)
            elif jmp_code == 'jo':
                tmp_sum = tmp1_expr + tmp2_expr
                if jmp_flag:
                    all_conditions.append(z3.Or(z3.And(tmp1_expr >= 0, tmp2_expr >= 0, tmp_sum < 0), z3.And(tmp1_expr < 0, tmp2_expr < 0, tmp_sum >= 0)))
                else:
                    all_conditions.append(z3.Or(z3.And(tmp1_expr >= 0, tmp2_expr >= 0, tmp_sum >= 0), z3.And(tmp1_expr < 0, tmp2_expr < 0, tmp_sum < 0)))
            elif jmp_code == 'jno':
                tmp_sum = tmp1_expr + tmp2_expr
                if jmp_flag:
                    all_conditions.append(z3.Or(z3.And(tmp1_expr >= 0, tmp2_expr >= 0, tmp_sum >= 0), z3.And(tmp1_expr < 0, tmp2_expr < 0, tmp_sum < 0)))
                else:
                    all_conditions.append(z3.Or(z3.And(tmp1_expr >= 0, tmp2_expr >= 0, tmp_sum < 0), z3.And(tmp1_expr < 0, tmp2_expr < 0, tmp_sum >= 0)))
            elif jmp_code == 'jc':
                if jmp_flag:
                    all_conditions.append(z3.ULT(tmp1_expr + tmp2_expr, tmp1_expr))
                else:
                    all_conditions.append(z3.Not(z3.ULT(tmp1_expr + tmp2_expr, tmp1_expr)))
            elif jmp_code == 'jnc':
                if jmp_flag:
                    all_conditions.append(z3.Not(z3.ULT(tmp1_expr + tmp2_expr, tmp1_expr)))
                else:
                    all_conditions.append(z3.ULT(tmp1_expr + tmp2_expr, tmp1_expr))
            elif jmp_code == 'jmp':
                continue
            else:
                exit(-1)
        elif cmp_code == 'test':
            
            jmp_code = conditional_jumps[i][1]
            jmp_flag = conditional_jumps[i][2]
            test_result = tmp1_expr & tmp2_expr
            test_size = test_result.size()
            
            if jmp_code == 'je' or jmp_code == 'jz':
                if jmp_flag:
                    all_conditions.append(test_result == z3.BitVecVal(0,test_size))
                else:
                    all_conditions.append(test_result != z3.BitVecVal(0,test_size))
            elif jmp_code == 'jne' or jmp_code == 'jnz':
                if jmp_flag:
                    all_conditions.append(test_result != z3.BitVecVal(0,test_size))
                else:
                    all_conditions.append(test_result == z3.BitVecVal(0,test_size))
            
            elif jmp_code == 'js':
                if jmp_flag:
                    all_conditions.append(z3.Extract(test_size-1,test_size-1,test_result) == z3.BitVecVal(1,1))
                else:
                    all_conditions.append(z3.Extract(test_size-1,test_size-1,test_result) != z3.BitVecVal(1,1))
            elif jmp_code == 'jns':
                if jmp_flag:
                    all_conditions.append(z3.Extract(test_size-1,test_size-1,test_result) != z3.BitVecVal(1,1))
                else:
                    all_conditions.append(z3.Extract(test_size-1,test_size-1,test_result) == z3.BitVecVal(1,1))
            
            elif jmp_code == 'jp':
                bv = z3.Extract(7, 0, test_result)
                for i in range(7):
                    num_ones += z3.Extract(i, i, bv)
                num_ones = num_ones.as_long()
                if jmp_flag:
                    all_conditions.append(num_ones%2 == 0)
                else:
                    all_conditions.append(num_ones%2 != 0)
            elif jmp_code == 'jnp':
                bv = z3.Extract(7, 0, test_result)
                for i in range(7):
                    num_ones += z3.Extract(i, i, bv)
                num_ones = num_ones.as_long()
                if jmp_flag:
                    all_conditions.append(num_ones%2 != 0)
                else:
                    all_conditions.append(num_ones%2 == 0)
            elif jmp_code == 'jmp':
                continue
            else:                
                exit(-1)
    return all_conditions

def solve_control_flow_exprs(conditional_jumps,operands_exprs_list,All_infos,source_dctx):
    
    solver = z3.Solver()
    conditions = get_conditions_from_control_flow(conditional_jumps,operands_exprs_list,All_infos,source_dctx)
    for condition in conditions:
        solver.add(condition)
    res = {}
    print(solver)
    
    if solver.check() == z3.sat:
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("no solution")
    return res
            

class ControlFlowConstraint():
    def __init__(self) -> None:
        self.conditional_jumps = [] 
        self.operands_exprs_list = [] 

    
    def fresh(self):
        self.conditional_jumps = [] 
        self.operands_exprs_list = [] 
    
    def get_z3_exprs_by_operands_list(self, source_addr, target_addr, dataflowgraph, z3_expr):
        
        
        cmp_list = dataflowgraph.cmp_list[source_addr][target_addr] 
        irsb_lists = [] 
        gap_source_addrs,gap_target_addrs = dataflowgraph.gap_addrs[source_addr][target_addr]
        for i in range(len(gap_source_addrs)):
            irsb_lists.append(dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]])
        operands_list = get_operands_by_cmp_list(cmp_list,irsb_lists)
        operands_Load_infos = []
        operands_exprs_list = []
        for i in range(len(operands_list)):
            tmp1,tmp2,size,dfg_pos = operands_list[i]
            
            if tmp1[0] == 't':
                tmp1_expr,tmp1_Load_infos = z3_expr.get_tmp_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,tmp1,dfg_pos)
            else:
                tmp1_expr = z3.BitVecVal(int(tmp1,16),int(size,10))
                tmp1_Load_infos = []
            if tmp2[0] == 't':
                tmp2_expr,tmp2_Load_infos = z3_expr.get_tmp_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,tmp2,dfg_pos)
            else:
                tmp2_expr = z3.BitVecVal(int(tmp2,16),int(size,10))
                tmp2_Load_infos = []
            operands_exprs_list.append((tmp1_expr,tmp2_expr))
            operands_Load_infos = generate_z3_exprs.remove_duplicates_by_first_element(operands_Load_infos + tmp1_Load_infos + tmp2_Load_infos)
        return operands_exprs_list,operands_Load_infos
    
    def get_control_flow_payload(self, source_addr, target_addr, target_count, target_block, dataflowgraph, z3_expr, source_dctx, DEBUG = True):
        
        
        conditional_jumps = find_conditional_jumps(target_block, source_addr, target_addr, target_count)
        self.conditional_jumps = conditional_jumps
        
        operands_exprs_list,operands_Load_infos = self.get_z3_exprs_by_operands_list(source_addr, target_addr, dataflowgraph, z3_expr)
        self.operands_exprs_list = operands_exprs_list
        if len(conditional_jumps) != len(operands_exprs_list):
            exit(-1)
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_addr][target_addr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_addr][target_addr][1]
        Store_infos,Load_infos = z3_expr.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        All_Load_infos = generate_z3_exprs.remove_duplicates_by_first_element(operands_Load_infos + Load_infos)
        All_infos = Store_infos + All_Load_infos
        All_infos = z3_expr.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        if DEBUG:
            z3_expr.add_ins_for_all_infos(All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs)
        
        tmp_result = solve_control_flow_exprs(conditional_jumps,operands_exprs_list,All_infos,source_dctx)
        
        result = {}
        for var in tmp_result:
            if "Load" in var:
                load_order = generate_z3_exprs.get_load_order(var,All_infos)
                result.update(generate_z3_exprs.solve_load_from_dctx(var,tmp_result[var],All_infos,source_dctx,result,load_order))
                result_hex = {}
                for addr in result:
                    
                    result_hex[hex(addr)] = hex(result[addr])   
        return result