import z3
import networkx as nx
import archinfo
import re
import multiprocessing
import time
import os
import json
from triton import *
from config.config import *
from . import control_flow_analyse
from .build_dfgs import DataFlowGraph

regs_list = ['eax','ebx','ecx','edx','esi','edi','ebp','esp','eip','eflags','rax','rbx','rcx','rdx','rsi','rdi','rbp','rsp','rip','r8','r9','r10','r11','r12','r13','r14','r15']

def get_register_name(arch, offset):
    
    if offset % (BITNESS // 8) != 0:
        offset -= 1
    for key in arch.register_list:
        reg_offset = arch.get_register_offset(key.name)
        if offset == reg_offset:
            return key.name

def calculate_depths(graph):
    
    
    topo_order = list(nx.topological_sort(graph))

    
    depths = {node: 0 for node in topo_order}

    
    for node in topo_order:
        
        max_depth = 0
        for pred in graph.predecessors(node):
            max_depth = max(max_depth, depths[pred])
        
        
        depths[node] = max_depth + 1

    return depths

def rename_reg(reg_name,z3_vars):
    
    num=0
    for key in z3_vars:
        if reg_name in key:
            num+=1
    new_reg_name=reg_name+'_'+str(num+1)
    return new_reg_name

def find_load_addr_vars(z3_expr):
    
    z3_str = str(z3_expr)
    
    pattern = r'Load_(t\d+)\b'
    matchs = re.findall(pattern,z3_str)
    return matchs

def find_relied_reg_vars(z3_expr):
    
    matches = []
    for reg_str in regs_list:
        if reg_str in str(z3_expr):
            matches.append(reg_str)
    return matches

def get_z3_expr_by_name(expr,var_name):
    
    if isinstance(expr, z3.BitVecRef) and expr.decl().name() == var_name:
        return expr
    
    for child in expr.children():
        result = get_z3_expr_by_name(child, var_name)
        if result is not None:
            return result
    
    return None

def get_z3_subexpressions_names(expr):
    
    names = []

    def helper(expr):
        expr_name = expr.decl().name()
        if isinstance(expr, z3.BitVecRef) and expr_name in regs_list:
            names.append(expr_name)
        elif isinstance(expr, z3.BitVecRef) and 'Load' in expr_name:
            names.append(expr_name)
        elif isinstance(expr, z3.BitVecNumRef):
            names.append(expr.as_long())
        else:
            for child in expr.children():
                helper(child)

    helper(expr)

    return names

def check_load_in_expr(expr):
    
    sub_exprs = get_z3_subexpressions_names(expr)
    for var in sub_exprs:
        if isinstance(var,str) and 'Load' in var:
            return var
    return None

def get_conditions_in_z3_expr(z3_expr,All_infos,source_dctx):
    
    
    sub_expr_names = get_z3_subexpressions_names(z3_expr)
    
    conditions = []
    for sub_expr_name in sub_expr_names:
        if sub_expr_name in regs_list:
            sub_reg_expr = get_z3_expr_by_name(z3_expr,sub_expr_name)
            
            value = source_dctx[1][sub_expr_name]
            z3_value = z3.BitVecVal(value,sub_reg_expr.size())
            conditions.append(z3.ULE(sub_reg_expr,z3_value))
            conditions.append(z3.UGE(sub_reg_expr,z3_value))
        elif isinstance(sub_expr_name,int):
            continue
        elif 'Load' in sub_expr_name:
            
            sub_load_expr = get_z3_expr_by_name(z3_expr,sub_expr_name)
            for i in range(len(All_infos)):
                if All_infos[i][0] == sub_expr_name:
                    
                    min_value = All_infos[i][6][0]
                    max_value = All_infos[i][6][1]
                    z3_min_value = z3.BitVecVal(min_value,sub_load_expr.size())
                    z3_max_value = z3.BitVecVal(max_value,sub_load_expr.size())
                    conditions.append(z3.ULE(sub_load_expr,z3_max_value))
                    conditions.append(z3.UGE(sub_load_expr,z3_min_value))
                    break
    return conditions

def evaluate_z3_expr_from_dctx(z3_expr,All_infos,source_dctx):
    
    
    conditions = get_conditions_in_z3_expr(z3_expr,All_infos,source_dctx)
    
    opt = z3.Optimize()
    for condition in conditions:
        opt.add(condition)
    min = opt.minimize(z3_expr)
    max = opt.maximize(z3_expr)
    opt.set('priority', 'box')
    opt.check()
    min = min.value().as_long()
    max = max.value().as_long()
    return min,max

def evaluate_mix_expr_from_dctx(conditional_jumps,operands_exprs_list,z3_expr,All_infos,source_dctx):
    
    
    data_conditions = get_conditions_in_z3_expr(z3_expr,All_infos,source_dctx)
    
    control_conditions = control_flow_analyse.get_conditions_from_control_flow(conditional_jumps,operands_exprs_list,All_infos,source_dctx)
    
    opt = z3.Optimize()
    for condition in data_conditions:
        opt.add(condition)
    for condition in control_conditions:
        opt.add(condition)
    min = opt.minimize(z3_expr)
    max = opt.maximize(z3_expr)
    opt.set('priority', 'box')
    opt.check()
    min = min.value().as_long()
    max = max.value().as_long()
    return min,max


def check_z3_expr_from_dctx(reg1_expr,All_infos1,reg2_expr,All_infos2,source_dctx):
    
    
    conditions1 = get_conditions_in_z3_expr(reg1_expr,All_infos1,source_dctx)
    
    
    conditions2 = get_conditions_in_z3_expr(reg2_expr,All_infos2,source_dctx)

    solver = z3.Solver()

    solver.add(reg1_expr == reg2_expr)

    for condition in conditions1 + conditions2:
        solver.add(condition)
    
    result = solver.check()

    if result == z3.sat:
        return True
    else:
        return False

def solve_data_flow_exprs(reg_expr,reg_value,All_infos,source_dctx):
    
    
    conditions = get_conditions_in_z3_expr(reg_expr,All_infos,source_dctx)
    
    solver = z3.Solver()
    reg_value = z3.BitVecVal(reg_value,reg_expr.size())
    solver.add(reg_expr == reg_value)
    for condition in conditions:
        solver.add(condition)
    res = {}
    if solver.check() == z3.sat:
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    return res

def check_subchain_load_vars(result,All_infos):
    
    load_order_dic = {}
    for var in result:
        if 'Load' in var:
            tmp_order = get_load_order(var,All_infos)
            load_order = [t[0] for t in tmp_order][::-1]
            load_order_dic[var] = '_' + '_'.join(map(str,load_order)) + '_'
    result = []
    for key, value in load_order_dic.items():
        for other_key, other_value in load_order_dic.items():
            if other_key != key:
                if value in other_value:
                    result.append((key,other_key))
                    break
    return result

def check_comchain_load_vars(result,All_infos):
    
    part_load_order_dic = {}
    for var in result:
        if 'Load' in var:
            tmp_order = get_load_order(var,All_infos)
            part_load_order = [t[0] for t in tmp_order][::-1]
            part_load_order_dic[var] = part_load_order
    result = []
    for key, part_load_order in part_load_order_dic.items():
        for other_key, other_part_load_order in part_load_order_dic.items():
            if other_key != key:
                i = 0
                while i < min(len(part_load_order),len(other_part_load_order)) and part_load_order[i] == other_part_load_order[i]:
                    i += 1
                if i >= 1 and i < len(part_load_order) and i < len(other_part_load_order):
                    load_order = get_load_order(key,All_infos)
                    other_load_order = get_load_order(other_key,All_infos)
                    if (not check_last_load_adr(load_order,len(load_order)-i)) and (not check_last_load_adr(other_load_order,len(other_load_order)-i)):
                        result.append((key,other_key,i-1))
    
    encountered_sets = set()
    new_result = []
    for tup in result:
        current_set = set(tup)  
        
        if tuple(current_set) not in encountered_sets:
            new_result.append(tup)
            encountered_sets.add(tuple(current_set))  
    return new_result


def find_tuple_index(lst, target):
    for index, tpl in enumerate(lst):
        if tpl[0] == target:
            return index

def get_subchain_load_conditons(subchain_load_vars, All_infos, source_dctx):
    
    conditions = []
    
    STle_addrs = []
    for i in range(len(All_infos)):
        if "Store" in All_infos[i][0]:
            STle_info = All_infos[i]
            start_addr = STle_info[5][0]
            
            if (STle_info[5][1]-STle_info[5][0]) == 0:
                value_bytes = int(STle_info[4].size() / 8)
                for j in range(value_bytes):
                    STle_addrs.append(start_addr+j)
    STle_addrs = list(set(STle_addrs))
    length = BITNESS // 8
    min_value = min(source_dctx[2])
    max_value = max(source_dctx[2])
    z3_min_value = z3.BitVecVal(min_value, length * 8)
    z3_max_value = z3.BitVecVal(max_value, length * 8)
    for sub_load_var,load_var in subchain_load_vars:
        load_order = get_load_order(load_var,All_infos)
        index_in_all_infos = find_tuple_index(All_infos, sub_load_var)
        index_in_load_order = find_tuple_index(load_order,index_in_all_infos)
        gap_addr = calculate_gap_addr(All_infos,load_order,index_in_load_order)
        sub_load_expr = z3.BitVec(sub_load_var, length * 8)
        load_expr = sub_load_expr + z3.BitVecVal(gap_addr, length * 8)
        conditions.append(z3.ULE(sub_load_expr,z3_max_value - length + 1))
        conditions.append(z3.UGE(sub_load_expr,z3_min_value))
        conditions.append(z3.ULE(load_expr,z3_max_value - length + 1))
        conditions.append(z3.UGE(load_expr,z3_min_value))
        for stle_addr in STle_addrs:
            stle_addr_expr = z3.BitVecVal(stle_addr, length * 8)
            conditions.append(z3.Distinct(sub_load_expr, stle_addr_expr))
            conditions.append(z3.Distinct(load_expr, stle_addr_expr))
    return conditions

def get_comchain_load_conditons(comchain_load_vars,All_infos,source_dctx):
    
    conditions = []
    
    STle_addrs = []
    for i in range(len(All_infos)):
        if "Store" in All_infos[i][0]:
            STle_info = All_infos[i]
            start_addr = STle_info[5][0]
            
            if (STle_info[5][1]-STle_info[5][0]) == 0:
                value_bytes = int(STle_info[4].size() / 8)
                for j in range(value_bytes):
                    STle_addrs.append(start_addr+j)
    STle_addrs = list(set(STle_addrs))
    length = BITNESS // 8
    min_value = min(source_dctx[2])
    max_value = max(source_dctx[2])
    z3_min_value = z3.BitVecVal(min_value, length * 8)
    z3_max_value = z3.BitVecVal(max_value, length * 8)
    for com_load_var1,com_load_var2,pos in comchain_load_vars:
        load_var_order1 = get_load_order(com_load_var1, All_infos)
        load_var_order2 = get_load_order(com_load_var2, All_infos)
        index1 = len(load_var_order1) - pos - 1
        index2 = len(load_var_order2) - pos - 1 
        com_load_var = All_infos[load_var_order1[index1][0]][0]
        gap_addr1 = calculate_gap_addr(All_infos, load_var_order1, index1)
        gap_addr2 = calculate_gap_addr(All_infos, load_var_order2, index2)
        com_load_expr = z3.BitVec(com_load_var, length * 8)
        next_load_expr1 = com_load_expr + z3.BitVecVal(gap_addr1, length * 8)
        next_load_expr2 = com_load_expr + z3.BitVecVal(gap_addr2, length * 8)
        conditions.append(z3.ULE(com_load_expr, z3_max_value - length + 1))
        conditions.append(z3.UGE(com_load_expr, z3_min_value))
        conditions.append(z3.ULE(next_load_expr1, z3_max_value - length + 1))
        conditions.append(z3.UGE(next_load_expr1, z3_min_value))
        conditions.append(z3.ULE(next_load_expr2, z3_max_value - length + 1))
        conditions.append(z3.UGE(next_load_expr2, z3_min_value))
        for stle_addr in STle_addrs:
            stle_addr_expr = z3.BitVecVal(stle_addr, length * 8)
            conditions.append(z3.Distinct(com_load_expr, stle_addr_expr))
            conditions.append(z3.Distinct(next_load_expr1, stle_addr_expr))
            conditions.append(z3.Distinct(next_load_expr2, stle_addr_expr))
    return conditions

def solve_mix_exprs(conditional_jumps,operands_exprs_list,reg_expr_list,reg_value_list,All_infos,source_dctx):
    
    solver = z3.Solver()
    conditions = control_flow_analyse.get_conditions_from_control_flow(conditional_jumps,operands_exprs_list,All_infos,source_dctx)
    for reg_expr in reg_expr_list:
        conditions.extend(get_conditions_in_z3_expr(reg_expr,All_infos,source_dctx))
    for condition in conditions:
        solver.add(condition)
    for i in range(len(reg_expr_list)):
        reg_value = reg_value_list[i]
        reg_expr = reg_expr_list[i]
        reg_value = z3.BitVecVal(reg_value,reg_expr.size())
        solver.add(reg_expr == reg_value)
    res = {}
    
    if solver.check() == z3.sat:
        
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("No solution")
    
    subchain_load_vars = check_subchain_load_vars(res,All_infos)
    
    new_conditions = get_subchain_load_conditons(subchain_load_vars,All_infos,source_dctx)
    
    comchain_load_vars = check_comchain_load_vars(res,All_infos)
    
    new_conditions.extend(get_comchain_load_conditons(comchain_load_vars,All_infos,source_dctx))

    for new_condition in new_conditions:
        solver.add(new_condition)
    res = {}
    
    if solver.check() == z3.sat:
        
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("No solution")
    
    result = []
    for sub_load_var,_ in subchain_load_vars:
        result.append((sub_load_var,res[sub_load_var]))
    for var in res:
        if (var,res[var]) not in result:
            result.append((var,res[var]))
    return result

def solve_data_exprs(reg_expr_list,reg_value_list,All_infos,source_dctx):
    
    solver = z3.Solver()
    conditions = []
    for reg_expr in reg_expr_list:
        conditions.extend(get_conditions_in_z3_expr(reg_expr,All_infos,source_dctx))
    for condition in conditions:
        solver.add(condition)
    for i in range(len(reg_expr_list)):
        reg_value = reg_value_list[i]
        reg_expr = reg_expr_list[i]
        reg_value = z3.BitVecVal(reg_value,reg_expr.size())
        solver.add(reg_expr == reg_value)
    res = {}
    
    if solver.check() == z3.sat:
        
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("No solution")
    
    subchain_load_vars = check_subchain_load_vars(res,All_infos)
    
    new_conditions = get_subchain_load_conditons(subchain_load_vars,All_infos,source_dctx)
    
    comchain_load_vars = check_comchain_load_vars(res,All_infos)
    
    new_conditions.extend(get_comchain_load_conditons(comchain_load_vars,All_infos,source_dctx))

    for new_condition in new_conditions:
        solver.add(new_condition)
    res = {}
    
    if solver.check() == z3.sat:
        
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("No solution")
    
    result = []
    for sub_load_var,_ in subchain_load_vars:
        result.append((sub_load_var,res[sub_load_var]))
    for var in res:
        if (var,res[var]) not in result:
            result.append((var,res[var]))
    return result

def get_load_order(Load_var,All_infos):
    
    load_order = []
    for i in range(len(All_infos)):
        if Load_var == All_infos[i][0]:
            addr_expr = All_infos[i][3]
            value_expr = All_infos[i][4]
            if value_expr == None:
                
                if check_load_in_expr(addr_expr) == None:
                    load_order.append((i,None))
                
                else:
                    load_order.append((i,True))
                    sub_exprs = get_z3_subexpressions_names(addr_expr)
                    for sub_expr in sub_exprs:
                        if isinstance(sub_expr, str) and 'Load' in sub_expr:
                            new_load_var = sub_expr
                            load_order.extend(get_load_order(new_load_var,All_infos))
            
            else:
                load_order.append((i,False))
                sub_exprs = get_z3_subexpressions_names(value_expr)
                for sub_expr in sub_exprs:
                    if isinstance(sub_expr, str) and 'Load' in sub_expr:
                        new_load_var = sub_expr
                        load_order.extend(get_load_order(new_load_var,All_infos))
            break
    return load_order


def solve_load_from_dctx(Load_var,Load_value,All_infos,source_dctx,res,load_order):
    
    length = BITNESS // 8
    
    STle_addrs = []
    for i in range(len(All_infos)):
        if "Store" in All_infos[i][0]:
            STle_info = All_infos[i]
            start_addr = STle_info[5][0]
            
            if (STle_info[5][1]-STle_info[5][0]) == 0:
                value_bytes = int(STle_info[4].size() / 8)
                for j in range(value_bytes):
                    STle_addrs.append(start_addr+j)
    STle_addrs = list(set(STle_addrs))
    
    for i in range(len(load_order)-1,-1,-1):
        if i == len(load_order)-1:
            if load_order[i][1] != None:
                print("Failed to solve the chain dependency for %s variable"%Load_var)
                exit(-1)
            addr_expr = All_infos[load_order[i][0]][3]
            conditions = get_conditions_in_z3_expr(addr_expr,All_infos,source_dctx)
            opt = z3.Optimize()
            for condition in conditions:
                opt.add(condition)
            min = opt.minimize(addr_expr)
            opt.set('priority', 'box')
            opt.check()
            min = min.value().as_long()
            
            if min not in res:
                for addr in range(min, min + 4):
                    res[addr] = 0
                
                if check_last_load_adr(load_order,i):
                    load_value = Load_value
                else:
                    
                    gap_addr = calculate_gap_addr(All_infos,load_order,i)
                    load_value = obtain_load_addr(All_infos,source_dctx,res,STle_addrs,gap_addr)
                    if load_value == None:
                        print("No suitable address was found")
                        exit(-1)
            else:
                load_value = 0
                for i in range(length):
                    load_value += res[min+i] << (i * 8)

            for i in range(length):
                res[min + i] = (load_value >> (i * 8)) & 0xFF
            new_load_addr = load_value
        else:
            
            if load_order[i][1] == True:
                addr_expr = All_infos[load_order[i][0]][3]
                old_load_addr_expr = get_z3_expr_by_name(addr_expr,All_infos[load_order[i+1][0]][0])
                substitute_dict = [(old_load_addr_expr,z3.BitVecVal(new_load_addr,old_load_addr_expr.size()))]
                addr_expr = z3.substitute(addr_expr,substitute_dict)
                conditions = get_conditions_in_z3_expr(addr_expr,All_infos,source_dctx)
                opt = z3.Optimize()
                for condition in conditions:
                    opt.add(condition)
                min = opt.minimize(addr_expr)
                opt.set('priority', 'box')
                opt.check()
                min = min.value().as_long()
                if min not in res:
                    
                    for addr in range(min, min + length):
                        res[addr] = 0
                    
                    if check_last_load_adr(load_order, i):
                        load_value = Load_value
                    else:
                        
                        gap_addr = calculate_gap_addr(All_infos,load_order,i)
                        load_value = obtain_load_addr(All_infos,source_dctx,res,STle_addrs,gap_addr)
                        if load_value == None:
                            print("No suitable address was found")
                            exit(-1)
                else:
                    load_value = 0
                    for i in range(length):
                        load_value += res[min+i] << (i * 8)
                
                for i in range(length):
                    res[min + i] = (load_value >> (i * 8)) & 0xFF
                new_load_addr = load_value
            else:
                
                continue
    return res

def check_last_load_adr(load_order,i):
    
    for j in range(i-1,-1,-1):
        if load_order[j][1] == True:
            return False
    return True

def obtain_load_addr(All_infos,source_dctx,res,STle_addrs,gap_addr):
    
    for addr in source_dctx[2]:
        if (addr + gap_addr) not in source_dctx[2]:
            continue
        length = BITNESS // 8
        for addr_i in range(addr,addr+length):
            if addr_i in STle_addrs or (addr_i+gap_addr) in STle_addrs:
                break
            if addr_i in res or (addr_i+gap_addr) in res:
                break
            if addr_i == addr + length - 1:
                return addr
    return None

def calculate_gap_addr(All_infos,load_order,i):
    
    for j in range(i-1,-1,-1):
        if load_order[j][1] == True:
            addr_expr = All_infos[load_order[j][0]][3]
            for child_expr in addr_expr.children():
                if isinstance(child_expr, z3.BitVecNumRef):
                    return child_expr.as_long()
            return 0
    return None
                
def remove_duplicates_by_first_element(a):
    
    seen = set()
    result = []
    for sublist in a:
        if sublist[0] not in seen:
            seen.add(sublist[0])
            result.append(sublist)
    return result

def find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,mem_op_name):
    
    pattern = r'_(\d+)'
    match = re.search(pattern,mem_op_name)
    dfg_pos = int(match.group(1))

    pattern = r'_(.*?)_'
    match = re.search(pattern,mem_op_name)
    new_tmp_name = match.group(1)
    new_irsb_list = irsb_list[gap_source_addrs[dfg_pos]][gap_target_addrs[dfg_pos]]
    if 'Store' in mem_op_name:
        pattern = r'STle\(%s\)'%new_tmp_name
    else:
        pattern = r'LDle:I\d+\(%s\)'%new_tmp_name
    for i in range(len(new_irsb_list)):
        ir_statement = new_irsb_list[i]
        match = re.search(pattern,ir_statement)
        if match:
            ir_pos = i
            break
    return dfg_pos,ir_pos

def handle_div(rvalue1,rvalue2,stmt):
    
    
    pattern = r'\d+'
    matches = re.findall(pattern, stmt.data.op)
    if 'Iop_DivU' in stmt.data.op:
        rvalue = z3.UDiv(rvalue1,rvalue2)
    elif 'Iop_DivS' in stmt.data.op:
        rvalue = rvalue1 / rvalue2
    elif 'Iop_DivModU' in stmt.data.op:
        u_mod_result = z3.URem(rvalue1,rvalue2)
        u_div_result = z3.UDiv(rvalue1,rvalue2)
        rvalue = (u_mod_result << int(matches[1])) + (u_div_result)
    elif 'Iop_DivModS' in stmt.data.op:
        s_mod_result = z3.SRem(rvalue1,rvalue2)
        s_div_result = rvalue1 / rvalue2
        if int(matches[0]) == int(matches[1]):
            gap_size = int(matches[0])
            rvalue = (z3.ZeroExt(gap_size,s_mod_result)<<int(matches[0])) + (z3.ZeroExt(gap_size,s_div_result))
        else:
            rvalue = (s_mod_result << int(matches[1])) + (s_div_result)
    return rvalue

def handle_mul(rvalue1,rvalue2,stmt):
    
    pattern = r'\d+'
    matches = re.findall(pattern, stmt.data.op)
    if 'Iop_MullS' in stmt.data.op:
        rvalue1 = z3.SignExt(int(matches[0])-rvalue1.size(),rvalue1)
        rvalue2 = z3.SignExt(int(matches[0])-rvalue2.size(),rvalue2)
        rvalue = rvalue1 * rvalue2
    else:
        rvalue1 = z3.ZeroExt(int(matches[0])-rvalue1.size(),rvalue1)
        rvalue2 = z3.ZeroExt(int(matches[0])-rvalue2.size(),rvalue2)
        rvalue = rvalue1 * rvalue2
    return rvalue

def handle_conversions(operand,stmt):
    
    pattern = r'\d+'
    matches = re.findall(pattern, stmt.data.op)
    size1 = int(matches[0])
    size2 = int(matches[1])
    if size1 != operand.size():
        print("The vector number of operands in VEX IR:%s is incorrect"%stmt)
        print("Number of operation digits: %d"%(operand.size()))
        exit(-1)
    gap_size = size2 - size1
    
    if "Uto" in stmt.data.op:
        rvalue=z3.ZeroExt(gap_size,operand)
    elif "Sto" in stmt.data.op:
        rvalue=z3.SignExt(gap_size,operand)
    
    elif 'HIto' in stmt.data.op:
        rvalue = z3.Extract(size1-1, size1-size2, operand)
    elif "to" in stmt.data.op:
        rvalue = z3.Extract(size2-1, 0, operand)
    return rvalue

def handle_cmp(rvalue1,rvalue2,stmt):
    
    pattern = r'\d+'
    matches = re.findall(pattern, stmt.data.op)
    size = int(matches[0])
    if size != rvalue1.size() or size!=rvalue2.size():
        print("The vector number of operands in VEX IR:%s is incorrect"%stmt)
        exit(-1)
    if 'EQ' in stmt.data.op:
        if z3.is_eq(rvalue1 == rvalue2):
            rvalue = z3.BoolVal(True)
        else:
            rvalue = z3.BoolVal(False)
    elif 'NE' in stmt.data.op:
        if z3.is_eq(rvalue1 == rvalue2):
            rvalue = z3.BoolVal(False)
        else:
            rvalue = z3.BoolVal(True)
    else:
        exit(-1)
    return rvalue

def convert_reg(reg_str):
    if ANALYSE_MODE == "X64":
        arch = archinfo.ArchAMD64()
    else:
        arch = archinfo.ArchX86()
    reg_offset = arch.registers[reg_str][0]
    new_reg_str = get_register_name(arch, reg_offset)
    if reg_offset % 4 == 0:
        reg_range = [0, arch.registers[reg_str][1]]
    else:
        reg_range = [1, arch.registers[reg_str][1] + 1]
    return new_reg_str, reg_range

class Z3Eepr():
    def __init__(self,memoryCache,codeCache) -> None:
        self.z3_vars={} 
        self.z3_var_to_stmt = {} 
        self.z3_store_value_vars = {} 
        self.z3_store_addr_vars = {} 
        self.reg_expr = {} 
        self.memoryCache = memoryCache
        self.codeCache = codeCache
        self.gap_source_addrs = []
        self.gap_target_addrs = []
        if ANALYSE_MODE == "X64":
            self.arch = archinfo.ArchAMD64()
        else:
            self.arch = archinfo.ArchX86()

    
    def fresh(self,memoryCache,codeCache):
        self.z3_vars={} 
        self.z3_var_to_stmt = {} 
        self.z3_store_value_vars = {} 
        self.z3_store_addr_vars = {} 
        self.reg_expr = {} 
        self.memoryCache = memoryCache
        self.codeCache = codeCache
        self.gap_source_addrs = []
        self.gap_target_addrs = []
        if ANALYSE_MODE == "X64":
            self.arch = archinfo.ArchAMD64()
        else:
            self.arch = archinfo.ArchX86()
    
    def vex_to_z3_in_dfg(self,dfg,irsb_list,source_adr,target_adr):
        
        
        
        reverse_depths = calculate_depths(dfg.reverse())
        depths = {} 
        max_depth = 0 
        for node in reverse_depths:
            depth = reverse_depths[node]
            if depth not in depths:
                depths[depth] = [node]
            else:
                depths[depth].append(node)
            if depth > max_depth:
                max_depth = depth
        z3_vars = {} 
        z3_var_to_stmt = {} 
        z3_store_value_vars = {} 
        z3_store_addr_vars = {} 
        maps = {} 

        current_depth=max_depth
        
        while current_depth>0:
            
            for node in depths[current_depth]:  
                
                stmt = node
                rvalue = None 
                
                if stmt.tag != 'Iex_Const':
                    exprs = list(stmt.expressions)
                    if stmt.tag == 'Ist_WrTmp': 
                        
                        if exprs[0].tag == 'Iex_Binop': 
                            if exprs[1].tag == 'Iex_RdTmp':
                                rvalue1 = z3_vars[f"t{exprs[1].tmp}"]
                            else:
                                rvalue1 = exprs[1].con.value
                                size = exprs[1].constants[0].size
                                rvalue1 = z3.BitVecVal(rvalue1, size)
                            if exprs[2].tag == 'Iex_RdTmp':
                                rvalue2 = z3_vars[f"t{exprs[2].tmp}"]
                            else:
                                rvalue2 = exprs[2].con.value
                                size = exprs[2].constants[0].size 
                                rvalue2 = z3.BitVecVal(rvalue2, size)
                            
                            if rvalue2.size()<rvalue1.size():
                                rvalue2 = z3.ZeroExt((rvalue1.size())-(rvalue2.size()),rvalue2)
                            if rvalue1.size()<rvalue2.size():
                                rvalue1 = z3.ZeroExt((rvalue2.size())-(rvalue1.size()),rvalue1)
                            
                            if stmt.data.op.startswith("Iop_Add"):
                                rvalue = (rvalue1 + rvalue2)
                            elif stmt.data.op.startswith("Iop_Sub"):
                                rvalue = (rvalue1 - rvalue2)
                            elif stmt.data.op.startswith("Iop_Mul"):
                                rvalue = (handle_mul(rvalue1,rvalue2,stmt))
                            elif stmt.data.op.startswith("Iop_Div"):
                                rvalue = (handle_div(rvalue1,rvalue2,stmt))
                            elif stmt.data.op.startswith("Iop_Or"):
                                rvalue = (rvalue1 | rvalue2)
                            elif stmt.data.op.startswith("Iop_And"):
                                rvalue = (rvalue1 & rvalue2)
                            elif stmt.data.op.startswith("Iop_Xor"):
                                rvalue = (rvalue1 ^ rvalue2)
                            elif stmt.data.op.startswith("Iop_Shl"):
                                rvalue = (rvalue1 << rvalue2)
                            elif stmt.data.op.startswith("Iop_Shr"):
                                rvalue = (z3.LShR(rvalue1,rvalue2))
                            elif stmt.data.op.startswith("Iop_Sar"):
                                rvalue = (rvalue1 >> rvalue2)
                            elif 'HLto' in stmt.data.op:
                                pattern = r'\d+'
                                matches = re.findall(pattern, stmt.data.op)
                                num0 = int(matches[0])
                                num1 = int(matches[1])
                                rvalue = (z3.ZeroExt((num1-num0), rvalue1) << num0) + z3.ZeroExt((num1-num0), rvalue2)
                            
                            elif 'Cmp' in stmt.data.op:
                                rvalue = (handle_cmp(rvalue1,rvalue2,stmt))

                        elif exprs[0].tag == 'Iex_Unop': 
                            if exprs[1].tag == 'Iex_RdTmp':
                                operand = z3_vars[f"t{exprs[1].tmp}"]
                            else:
                                operand = exprs[1].con.value
                                size = exprs[1].constants[0].size
                                operand = z3.BitVecVal(operand, size) 
                            
                            
                            if "to" in stmt.data.op:
                                rvalue = handle_conversions(operand,stmt)
                            
                            elif "Not" in stmt.data.op:
                                rvalue = ~operand
                            
                            elif "Neg" in stmt.data.op:
                                rvalue = z3.BitVecNeg(operand)
                        
                        elif exprs[0].tag == 'Iex_RdTmp': 
                            operand = z3_vars[f"t{exprs[0].tmp}"]
                            rvalue = operand
                            
                        elif exprs[0].tag == 'Iex_Const': 
                            rvalue = exprs[0].con.value
                            size = exprs[0].constants[0].size
                            rvalue = z3.BitVecVal(rvalue, size)

                        elif exprs[0].tag == 'Iex_Get': 
                            
                            offset = exprs[0].offset 
                            reg_name=get_register_name(self.arch,offset) 
                            type = exprs[0].ty
                            pattern = r'Ity_I(\d+)'
                            match = re.search(pattern,type)
                            size = int(match.group(1))
                            pre_nodes=list(dfg.predecessors(node)) 
                            if len(pre_nodes)==0: 
                                z3_vars[reg_name]=z3.BitVec(reg_name,BITNESS) 
                                z3_var_to_stmt[reg_name] = stmt 
                                maps[node]= reg_name 
                            else:
                                pre_node = pre_nodes[0]
                                reg_name = maps[pre_node]  
                            rvalue = z3.Extract(size-1, 0, z3_vars[reg_name])

                        elif exprs[0].tag == 'Iex_Load':
                            type = exprs[0].ty
                            pattern = r'Ity_I(\d+)'
                            match = re.search(pattern,type)
                            
                            size = int(match.group(1)) 
                            if exprs[1].tag == 'Iex_RdTmp':
                                var_name = "Load_"+f"t{exprs[1].tmp}"
                            else:
                                var_name = "Load_"+str(exprs[1].con.value)
                            z3_vars[var_name] = z3.BitVec(var_name,size) 
                            rvalue = z3_vars[var_name] 

                        elif exprs[0].tag == 'Iex_ITE':
                            if exprs[1].tag == 'Iex_RdTmp':
                                condition = z3_vars[f"t{exprs[1].tmp}"]
                            else:
                                condition = exprs[1].con.value
                                size = exprs[1].constants[0].size
                                condition = z3.BitVecVal(condition, size)
                            if exprs[2].tag == 'Iex_RdTmp':
                                false = z3_vars[f"t{exprs[2].tmp}"]
                            else:
                                false = exprs[2].con.value
                                size = exprs[2].constants[0].size 
                                false = z3.BitVecVal(false, size)
                            if exprs[3].tag == 'Iex_RdTmp':
                                true = z3_vars[f"t{exprs[3].tmp}"]
                            else:
                                true = exprs[3].con.value
                                size = exprs[3].constants[0].size 
                                true = z3.BitVecVal(true, size) 
                            rvalue = z3.If(condition,true,false)

                        if rvalue == None: 
                            pass
                            
                        lvalue_name = f"t{stmt.tmp}"
                        z3_vars[lvalue_name] = rvalue
                        z3_var_to_stmt[lvalue_name] = stmt

                    elif stmt.tag == 'Ist_Store': 
                        if exprs[0].tag == 'Iex_RdTmp':
                            var_name = "Store_"+f"t{exprs[0].tmp}"
                        elif exprs[0].tag == 'Iex_Const':
                            var_name = "Store_"+str(exprs[0].con.value)
                        if exprs[1].tag == 'Iex_RdTmp':
                            rvalue = z3_vars[f"t{exprs[1].tmp}"]
                        else:
                            rvalue = exprs[1].con.value
                            size = exprs[1].con.size
                            rvalue = z3.BitVecVal(rvalue, size)

                        if rvalue == None:
                            exit(-1)
                        z3_vars[var_name]= rvalue
                        z3_var_to_stmt[var_name] = stmt
                        z3_store_value_vars[var_name]=rvalue 
                        z3_store_addr_vars[var_name]=z3_vars[f"t{exprs[0].tmp}"]

                    elif stmt.tag == 'Ist_Put': 
                        offset = stmt.offset 
                        
                        
                        if exprs[0].tag == 'Iex_RdTmp':
                            rvalue = z3_vars[f"t{exprs[0].tmp}"]
                            size = rvalue.size()
                        elif exprs[0].tag == 'Iex_Const':
                            rvalue = exprs[0].con.value
                            size = exprs[0].con.size
                            rvalue = z3.BitVecVal(rvalue, size)
                        
                        if rvalue == None:
                            exit(-1)
                        z3_vars,new_reg_name = self.update_reg_exprs(z3_vars,irsb_list,z3_var_to_stmt,offset,size,rvalue)
                        
                        
                        
                        z3_var_to_stmt[new_reg_name] = stmt
                        maps[node]=new_reg_name
                
            current_depth-=1 

        
        for var in z3_vars:
            z3_vars[var] = z3.simplify(z3_vars[var])

        
        for store_var in z3_store_value_vars:
            z3_store_value_vars[store_var] = z3.simplify(z3_store_value_vars[store_var])
        
        
        for store_var in z3_store_addr_vars:
            z3_store_addr_vars[store_var] = z3.simplify(z3_store_addr_vars[store_var])

        if source_adr not in self.z3_vars.keys():
            self.z3_vars[source_adr]={}
        self.z3_vars[source_adr][target_adr]=z3_vars
        if source_adr not in self.z3_var_to_stmt.keys():
            self.z3_var_to_stmt[source_adr]={}
        self.z3_var_to_stmt[source_adr][target_adr]=z3_var_to_stmt
        if source_adr not in self.z3_store_value_vars.keys():
            self.z3_store_value_vars[source_adr]={}
        self.z3_store_value_vars[source_adr][target_adr]=z3_store_value_vars
        if source_adr not in self.z3_store_addr_vars.keys():
            self.z3_store_addr_vars[source_adr]={}
        self.z3_store_addr_vars[source_adr][target_adr]=z3_store_addr_vars

    def resolve_load_variables(self, source_addr, target_addr, expr):
        
        resolved_load_exprs = {}

        
        load_vars = find_load_addr_vars(expr)
        if load_vars is not None:
            
            for load_var in load_vars:
                load_expr = self.z3_vars[source_addr][target_addr][load_var]
                resolved_load_exprs[load_var] = load_expr
                resolved_load_exprs.update(self.resolve_load_variables(source_addr,target_addr,load_expr))

        return resolved_load_exprs

    def rename_load_vars(self,expr,source_adr,target_adr,i):
        
        substitute_dict = []
        load_vars = find_load_addr_vars(expr)
        for load_var in load_vars:
            z3_load_var = self.z3_vars[source_adr][target_adr]['Load_'+ load_var]
            new_load_var_name = 'Load_'+ load_var + '_' + str(i)
            new_z3_load_var = z3.BitVec(new_load_var_name,z3_load_var.size())
            substitute_dict.append((z3_load_var,new_z3_load_var))
        new_expr = z3.substitute(expr,substitute_dict) 
        return new_expr
    
    def get_stle_exprs_in_dfgs(self,irsb_list,gap_source_addrs,gap_target_addrs):
        
        result_relied_load_addr_exprs = {} 
        Store_info = [] 
        Load_info = [] 
        
        dfg_nums = len(gap_source_addrs)
        
        for m in range(dfg_nums):
            z3_store_value_vars = self.z3_store_value_vars[gap_source_addrs[m]][gap_target_addrs[m]]
            z3_store_addr_vars = self.z3_store_addr_vars[gap_source_addrs[m]][gap_target_addrs[m]]
            
            for stle_var in z3_store_value_vars:
                
                for i in range(m,-1,-1):             
                    update_exprs = [] 
                    if i == m:
                        result_value_expr = z3_store_value_vars[stle_var]
                        result_addr_expr = z3_store_addr_vars[stle_var]
                        update_exprs.append(result_value_expr)
                        update_exprs.append(result_addr_expr)
                        result_value_expr = self.rename_load_vars(result_value_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                        result_addr_expr = self.rename_load_vars(result_addr_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                    else:
                        
                        for reg_str in value_relied_reg_vars:
                            new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                            var_name = reg_str
                            
                            result_value_expr = z3.simplify(result_value_expr)
                            reg_expr = get_z3_expr_by_name(result_value_expr,var_name)
                            
                            new_reg_expr = z3.Extract(reg_expr.size()-1,0,new_reg_expr)
                            substitute_dict = [(reg_expr,new_reg_expr)]
                            result_value_expr = z3.substitute(result_value_expr,substitute_dict)
                            update_exprs.append(new_reg_expr)
                            result_value_expr = self.rename_load_vars(result_value_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                        
                        for reg_str in addr_relied_reg_vars:
                            new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                            var_name = reg_str
                            result_addr_expr = z3.simplify(result_addr_expr)
                            reg_expr = get_z3_expr_by_name(result_addr_expr,var_name)
                            substitute_dict = [(reg_expr,new_reg_expr)]
                            result_addr_expr = z3.substitute(result_addr_expr,substitute_dict)
                            update_exprs.append(new_reg_expr)
                            result_addr_expr = self.rename_load_vars(result_addr_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                        
                        for result_load_addr_var in result_relied_load_addr_exprs:
                            result_load_expr = result_relied_load_addr_exprs[result_load_addr_var]
                            relied_reg_vars = find_relied_reg_vars(result_load_expr)
                            for reg_str in relied_reg_vars:
                                new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                                var_name = reg_str
                                result_load_expr = z3.simplify(result_load_expr)
                                reg_expr = get_z3_expr_by_name(result_load_expr,var_name)
                                substitute_dict = [(reg_expr,new_reg_expr)]
                                result_relied_load_addr_exprs[result_load_addr_var] = z3.substitute(result_relied_load_addr_exprs[result_load_addr_var],substitute_dict)
                                update_exprs.append(new_reg_expr)

                    
                    value_relied_reg_vars = find_relied_reg_vars(result_value_expr)
                    
                    addr_relied_reg_vars = find_relied_reg_vars(result_addr_expr)
                    
                    relied_load_addr_exprs = {} 
                    new_relied_load_addr_exprs = {}
                    for update_expr in update_exprs:
                        relied_load_addr_exprs.update(self.resolve_load_variables(gap_source_addrs[i],gap_target_addrs[i],update_expr))
                    for relied_load_var in relied_load_addr_exprs:
                        new_relied_load_addr_exprs[relied_load_var + '_' + str(i)] = self.rename_load_vars(relied_load_addr_exprs[relied_load_var],gap_source_addrs[i],gap_target_addrs[i],i)
                    result_relied_load_addr_exprs.update(new_relied_load_addr_exprs)
            
                
                result_value_expr = z3.simplify(result_value_expr)
                result_addr_expr = z3.simplify(result_addr_expr)
                for result_load_addr_var in result_relied_load_addr_exprs:
                    result_relied_load_addr_exprs[result_load_addr_var] = z3.simplify(result_relied_load_addr_exprs[result_load_addr_var])
                dfg_pos,ir_pos = find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,stle_var + '_' + str(m))

                
                Store_info.append([stle_var + '_' + str(m),dfg_pos,ir_pos,result_addr_expr,result_value_expr])

                
                for result_load_addr_var in result_relied_load_addr_exprs:
                    result_load_var = 'Load_' + result_load_addr_var
                    dfg_pos,ir_pos = find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,result_load_var)
                    Load_info.append([result_load_var,dfg_pos,ir_pos,result_relied_load_addr_exprs[result_load_addr_var]])
                result_relied_load_addr_exprs = {}
        
        
        Load_info = [list(x) for x in set(tuple(x) for x in Load_info)]
        return Store_info,Load_info

    def update_reg_exprs(self, z3_vars, irsb_list, z3_var_to_stmt, offset, size, rvalue):
        
        location = -1
        reg_name = get_register_name(self.arch,offset)
        new_reg_name = rename_reg(reg_name,z3_vars) 
        for var in z3_vars:
            if reg_name in var:
                stmt = z3_var_to_stmt[var]
                
                index = irsb_list.index(str(stmt))
                if index > location:
                    location = index
                    current_reg_expr = z3_vars[var]
        if offset % (BITNESS // 8) == 0:
            if size == BITNESS:
                reg_z3_expr = rvalue
            else:
                reg_z3_expr = z3.ZeroExt(size,z3.Extract(BITNESS - 1, size, current_reg_expr)) << size + z3.ZeroExt(BITNESS - size,rvalue)
        else:
            
            reg_z3_expr = z3.ZeroExt(BITNESS - 8, z3.Extract(7, 0, current_reg_expr)) + \
                            (z3.ZeroExt(BITNESS - 8, z3.Extract(7, 0, rvalue))) << 8 + \
                                z3.ZeroExt(16, z3.Extract(BITNESS - 1, 16, current_reg_expr)) << 16 
        z3_vars[new_reg_name] = reg_z3_expr
        return z3_vars,new_reg_name

                    
    def get_reg_exprs(self, irsb_list, source_adr, target_adr, reg_str):
        
        location = -1
        flag = 0
        z3_vars = self.z3_vars[source_adr][target_adr]
        
        reg_z3_expr = z3.BitVecVal(0, BITNESS)
        for var in z3_vars:
            if reg_str in var:
                stmt = self.z3_var_to_stmt[source_adr][target_adr][var]
                
                index = irsb_list[source_adr][target_adr].index(str(stmt))
                if index > location:
                    location = index
                    reg_z3_expr = z3_vars[var]
                    flag = 1

        if flag == 0:
            reg_z3_expr = z3.BitVec(reg_str, BITNESS)
        return reg_z3_expr
    
    def get_reg_exprs_in_dfgs(self,irsb_list,gap_source_addrs,gap_target_addrs,reg_str):
        
        
        reg_str, reg_len_range = convert_reg(reg_str)
        result_load_exprs = {} 
        result_Load_infos = [] 
        relied_reg_vars = [] 
        for i in range(len(gap_source_addrs)-1,-1,-1):
            update_exprs = [] 
            if i == len(gap_source_addrs)-1:
                result_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                update_exprs.append(result_expr)
                
                result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
            else:
                
                for reg_str in relied_reg_vars:
                    new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                    var_name = reg_str
                    result_expr = z3.simplify(result_expr)
                    reg_expr = get_z3_expr_by_name(result_expr,var_name)
                    substitute_dict = [(reg_expr,new_reg_expr)]
                    result_expr = z3.substitute(result_expr,substitute_dict)
                    update_exprs.append(new_reg_expr)
                    result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                
                for result_load_addr_var in result_load_exprs:
                    result_load_expr = result_load_exprs[result_load_addr_var]
                    relied_reg_vars = find_relied_reg_vars(result_load_expr)
                    for reg_str in relied_reg_vars:
                        new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                        var_name = reg_str
                        result_load_expr = z3.simplify(result_load_expr)
                        reg_expr = get_z3_expr_by_name(result_load_expr,var_name)
                        substitute_dict = [(reg_expr,new_reg_expr)]
                        result_load_exprs[result_load_addr_var] = z3.substitute(result_load_exprs[result_load_addr_var],substitute_dict)
                        
                        result_load_exprs[result_load_addr_var] = self.rename_load_vars(result_load_exprs[result_load_addr_var],gap_source_addrs[i],gap_target_addrs[i],i)
                        update_exprs.append(new_reg_expr)
                        

            
            relied_reg_vars = find_relied_reg_vars(result_expr)
            
            relied_load_exprs = {} 
            new_relied_load_exprs = {}
            for update_expr in update_exprs:
                relied_load_exprs.update(self.resolve_load_variables(gap_source_addrs[i],gap_target_addrs[i],update_expr))
            for relied_load_var in relied_load_exprs:
                new_relied_load_exprs[relied_load_var + '_' + str(i)] = self.rename_load_vars(relied_load_exprs[relied_load_var],gap_source_addrs[i],gap_target_addrs[i],i)
            result_load_exprs.update(new_relied_load_exprs)
        
        
        result_expr = z3.simplify(result_expr)
        for result_load_addr_var in result_load_exprs:
            result_load_exprs[result_load_addr_var] = z3.simplify(result_load_exprs[result_load_addr_var])

        
        for result_load_addr_var in result_load_exprs:
            result_load_var = 'Load_' + result_load_addr_var
            dfg_pos,ir_pos = find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,result_load_var)
            result_Load_infos.append([result_load_var,dfg_pos,ir_pos,result_load_exprs[result_load_addr_var]])

        result_expr = z3.Extract(reg_len_range[1] * 8 - 1, reg_len_range[0] * 8, result_expr)
        return result_expr,result_Load_infos
    
    def get_tmp_exprs(self, source_adr, target_adr, tmp_str):
        
        tmp_z3_expr = None
        z3_vars = self.z3_vars[source_adr][target_adr]
        tmp_z3_expr = z3_vars[tmp_str]
        return tmp_z3_expr

    def get_tmp_exprs_in_dfgs(self,irsb_list,gap_source_addrs,gap_target_addrs,tmp_str,dfg_pos):
        
        result_load_exprs = {} 
        result_Load_infos = [] 
        relied_reg_vars = [] 
        for i in range(dfg_pos,-1,-1):
            update_exprs = [] 
            if i == dfg_pos:
                result_expr = self.get_tmp_exprs(gap_source_addrs[i],gap_target_addrs[i],tmp_str)
                update_exprs.append(result_expr)
                
                result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
            else:
                
                for reg_str in relied_reg_vars:
                    new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                    var_name = reg_str
                    result_expr = z3.simplify(result_expr)
                    reg_expr = get_z3_expr_by_name(result_expr,var_name)
                    substitute_dict = [(reg_expr,new_reg_expr)]
                    result_expr = z3.substitute(result_expr,substitute_dict)
                    update_exprs.append(new_reg_expr)
                    result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                
                for result_load_addr_var in result_load_exprs:
                    result_load_expr = result_load_exprs[result_load_addr_var]
                    relied_reg_vars = find_relied_reg_vars(result_load_expr)
                    for reg_str in relied_reg_vars:
                        new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                        var_name = reg_str
                        result_load_expr = z3.simplify(result_load_expr)
                        reg_expr = get_z3_expr_by_name(result_load_expr,var_name)
                        substitute_dict = [(reg_expr,new_reg_expr)]
                        result_load_exprs[result_load_addr_var] = z3.substitute(result_load_exprs[result_load_addr_var],substitute_dict)
                        
                        result_load_exprs[result_load_addr_var] = self.rename_load_vars(result_load_exprs[result_load_addr_var],gap_source_addrs[i],gap_target_addrs[i],i)
                        update_exprs.append(new_reg_expr)
                        

            
            relied_reg_vars = find_relied_reg_vars(result_expr)
            
            relied_load_exprs = {} 
            new_relied_load_exprs = {}
            for update_expr in update_exprs:
                relied_load_exprs.update(self.resolve_load_variables(gap_source_addrs[i],gap_target_addrs[i],update_expr))
            for relied_load_var in relied_load_exprs:
                new_relied_load_exprs[relied_load_var + '_' + str(i)] = self.rename_load_vars(relied_load_exprs[relied_load_var],gap_source_addrs[i],gap_target_addrs[i],i)
            result_load_exprs.update(new_relied_load_exprs)
        
        
        result_expr = z3.simplify(result_expr)
        for result_load_addr_var in result_load_exprs:
            result_load_exprs[result_load_addr_var] = z3.simplify(result_load_exprs[result_load_addr_var])

        
        for result_load_addr_var in result_load_exprs:
            result_load_var = 'Load_' + result_load_addr_var
            dfg_pos,ir_pos = find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,result_load_var)
            result_Load_infos.append([result_load_var,dfg_pos,ir_pos,result_load_exprs[result_load_addr_var]])

        return result_expr,result_Load_infos

    def get_reg_range_by_vsa(self,dataflowgraph: DataFlowGraph,source_adr,target_adr,reg_str,source_dctx,DEBUG = True):
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])

        
        reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_str)
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        
        
        
        if DEBUG:
            self.add_ins_for_all_infos(All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs)
        min,max = evaluate_z3_expr_from_dctx(reg_expr,All_infos,source_dctx)
        return min,max
    
    def get_mix_range_by_vsa(self,target_block, dataflowgraph, path_constraint, source_adr, target_adr, target_count, reg_str, source_dctx,DEBUG = True):
        
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        
        reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_str)
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        
        
        conditional_jumps = control_flow_analyse.find_conditional_jumps(target_block, source_adr, target_adr, target_count)        
        operands_exprs_list,operands_Load_infos = path_constraint.get_z3_exprs_by_operands_list(source_adr, target_adr, dataflowgraph, self)
        path_constraint.operands_exprs_list = operands_exprs_list
        if len(conditional_jumps) != len(operands_exprs_list):
            exit(-1)
        All_infos += operands_Load_infos
        All_infos = remove_duplicates_by_first_element(All_infos)
        
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)

        
        if DEBUG:
            self.add_ins_for_all_infos(All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs)
        min,max = evaluate_mix_expr_from_dctx(conditional_jumps,operands_exprs_list,reg_expr,All_infos,source_dctx)
        return min,max
    
    def get_expr_range_by_vsa(self,target_block, dataflowgraph, path_constraint, source_adr, target_adr, target_count, reg_dic, source_dctx,DEBUG = False):
        
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        
        if type(reg_dic) == dict:
            reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['base'])
            if reg_dic['idx'] != None:
                index_reg_expr, index_reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['idx'])
                index_reg_expr = index_reg_expr * z3.BitVecVal(reg_dic['imm1'], index_reg_expr.size())
                reg_load_infos += index_reg_load_infos
                reg_expr += index_reg_expr 
            reg_expr += z3.BitVecVal(reg_dic['imm2'], reg_expr.size())
        elif type(reg_dic) == str:
            reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic)
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        
        
        conditional_jumps = control_flow_analyse.find_conditional_jumps(target_block, source_adr, target_adr, target_count)        
        operands_exprs_list,operands_Load_infos = path_constraint.get_z3_exprs_by_operands_list(source_adr, target_adr, dataflowgraph, self)
        path_constraint.operands_exprs_list = operands_exprs_list
        if len(conditional_jumps) <= len(operands_exprs_list):
            operands_exprs_list = operands_exprs_list[0:len(conditional_jumps)]
        else:
            exit(-1)
        All_infos += operands_Load_infos
        All_infos = remove_duplicates_by_first_element(All_infos)
        
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)

        
        
        
        
        
        
        
        
        
        
        
        
        
        
        
        if DEBUG:
            self.add_ins_for_all_infos(All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs)
        min,max = evaluate_mix_expr_from_dctx(conditional_jumps,operands_exprs_list,reg_expr,All_infos,source_dctx)
        return min,max
    
    def check_data_dependency_by_vsa(self,dataflowgraph,source_adr,target1_adr,reg1_dic,target2_adr,reg2_dic,source_dctx):
        
        gap_source_addrs1 = dataflowgraph.gap_addrs[source_adr][target1_adr][0]
        gap_target_addrs1 = dataflowgraph.gap_addrs[source_adr][target1_adr][1]
        
        for i in range(len(gap_source_addrs1)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs1[i]][gap_target_addrs1[i]],dataflowgraph.irsb_list[gap_source_addrs1[i]][gap_target_addrs1[i]],gap_source_addrs1[i],gap_target_addrs1[i])
        
        
        if type(reg1_dic) == dict:
            reg1_expr,reg_load_infos1 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1,reg1_dic['base'])
            if reg1_dic['idx'] != None:
                index_reg_expr, index_reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1,reg1_dic['idx'])
                index_reg_expr = index_reg_expr * z3.BitVecVal(reg_dic['imm1'], index_reg_expr.size())
                reg_load_infos1 += index_reg_load_infos
                reg1_expr += index_reg_expr 
            reg1_expr += z3.BitVecVal(reg1_dic['imm2'], reg1_expr.size())
        elif type(reg1_dic) == str:
            reg1_expr,reg_load_infos1 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1,reg1_dic)
        
        Store_infos1,Load_infos1 = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1)
        
        reg_load_infos1 = remove_duplicates_by_first_element(reg_load_infos1 + Load_infos1)
        
        All_infos1 = Store_infos1 + reg_load_infos1
        
        All_infos1 = self.addr_and_value_set_analyse(All_infos1,source_dctx,gap_source_addrs1,gap_target_addrs1)
        
        gap_source_addrs2 = dataflowgraph.gap_addrs[source_adr][target2_adr][0]
        gap_target_addrs2 = dataflowgraph.gap_addrs[source_adr][target2_adr][1]
        
        for i in range(len(gap_source_addrs2)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs2[i]][gap_target_addrs2[i]],dataflowgraph.irsb_list[gap_source_addrs2[i]][gap_target_addrs2[i]],gap_source_addrs2[i],gap_target_addrs2[i])
        
        
        if type(reg2_dic) == dict:
            reg2_expr,reg_load_infos2 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2,reg2_dic['base'])
            if reg2_dic['idx'] != None:
                index_reg_expr, index_reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2,reg1_dic['idx'])
                index_reg_expr = index_reg_expr * z3.BitVecVal(reg2_dic['imm1'], index_reg_expr.size())
                reg_load_infos2 += index_reg_load_infos
                reg2_expr += index_reg_expr 
            reg2_expr += z3.BitVecVal(reg2_dic['imm2'], reg2_expr.size())
        elif type(reg2_dic) == str:
            reg2_expr,reg_load_infos2 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2,reg2_dic)
        
        
        Store_infos2,Load_infos2 = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2)
        
        reg_load_infos2 = remove_duplicates_by_first_element(reg_load_infos2 + Load_infos2)
        
        All_infos2 = Store_infos2 + reg_load_infos2
        
        All_infos2 = self.addr_and_value_set_analyse(All_infos2,source_dctx,gap_source_addrs2,gap_target_addrs2)
        
        if check_z3_expr_from_dctx(reg1_expr,All_infos1,reg2_expr,All_infos2,source_dctx):
            return True
        else:
            return False
            
    def add_ins_for_all_infos(self,All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs):
        
        dfg_nums = len(gap_source_addrs)
        ins_list = dataflowgraph.ins_list[gap_source_addrs[0]][gap_target_addrs[-1]]
        for i in range(len(All_infos)):
            var_name = All_infos[i][0]
            dfg_pos = All_infos[i][1]
            ir_pos = All_infos[i][2]
            source_addr = gap_source_addrs[dfg_pos]
            target_addr = gap_target_addrs[dfg_pos]
            irsb_list = dataflowgraph.irsb_list[source_addr][target_addr]
            for j in range(ir_pos,-1,-1):
                if "IMark_" in irsb_list[j]:
                    imark_str = irsb_list[j]
                    pattern = r'_(\d+)'
                    match = re.search(pattern,imark_str)
                    current_ins_pos = int(match.group(1)) + 1
                    ins_pos = dfg_pos * 99 + current_ins_pos
                    All_infos[i].append(ins_list[ins_pos-1])
                    break

    def addr_and_value_set_analyse(self,All_infos,source_dctx,gap_source_addrs,gap_target_addrs,DEBUG = True):
        
        
        for i in range(len(All_infos)):
            if 'Load' in All_infos[i][0]:
                All_infos[i].append(None)

        All_infos = sorted(All_infos,key=lambda x: (x[1], x[2]))
        for i in range(len(All_infos)):
            var_name = All_infos[i][0]
            if 'Store' in var_name:
                
                addr_expr = All_infos[i][3]
                addr_min,addr_max = evaluate_z3_expr_from_dctx(addr_expr,All_infos,source_dctx)
                All_infos[i].append((addr_min,addr_max))
                
                value_expr = All_infos[i][4]
                value_min,value_max = evaluate_z3_expr_from_dctx(value_expr,All_infos,source_dctx)
                All_infos[i].append((value_min,value_max))
            elif 'Load' in var_name:
                
                addr_expr = All_infos[i][3]
                addr_min,addr_max = evaluate_z3_expr_from_dctx(addr_expr,All_infos,source_dctx)
                All_infos[i].append((addr_min,addr_max))
                
                flag = 0 
                for j in range(i,-1,-1):
                    if 'Store' in All_infos[j][0]:
                        if All_infos[j][5][0] == All_infos[i][5][0] and All_infos[j][5][1] == All_infos[i][5][1] and (All_infos[j][5][1]-All_infos[j][5][0]) == 0:
                            
                            All_infos[i][4] = All_infos[j][4]
                            
                            All_infos[i].append((All_infos[j][6][0],All_infos[j][6][1]))
                            flag = 1
                            break
                
                if flag == 0:
                    
                    size = self.get_size_from_load_name(All_infos[i][0],gap_source_addrs,gap_target_addrs)
                    if (addr_max - addr_min) > 10000:
                        for adr in source_dctx[2]:
                            if adr >= addr_min and adr <=addr_max:
                                All_infos[i].append((0,pow(2,size)-1))
                                flag = 1
                                break
                        if flag == 0:
                            exit(0)
                    else:
                        for addr in range(addr_min,addr_max+1):
                            if addr == addr_min:
                                min,max = self.get_range_from_load_addr(source_dctx, addr, int(size/8))
                            else:
                                tmp_min,tmp_max = self.get_range_from_load_addr(source_dctx, addr, int(size/8))
                                if tmp_min < min:
                                    min = tmp_min
                                if tmp_max > max:
                                    max = tmp_max
                        All_infos[i].append((min,max))
        return All_infos
    
    def get_size_from_load_name(self,Load_var_name,gap_source_addrs,gap_target_addrs):
        
        pattern = r'_(\d+)'
        match = re.search(pattern,Load_var_name)
        dfg_pos = int(match.group(1))
        pattern = r'(.*?)_\d+'
        match = re.search(pattern,Load_var_name)
        var_name = match.group(1)
        size = self.z3_vars[gap_source_addrs[dfg_pos]][gap_target_addrs[dfg_pos]][var_name].size()
        return size
    
    def get_range_from_load_addr(self,dctx,load_addr,size):
        
        load_value = z3.BitVecVal(0,size*8)
        for index in range(size):
            current_load_addr = load_addr + index
            
            if current_load_addr in dctx[2]:
                tainted_var = z3.BitVec(str(current_load_addr),8)
                load_value += (z3.ZeroExt(size*8-8,tainted_var) << (index*8))

            
            elif current_load_addr in dctx[0]:
                load_value += (z3.ZeroExt(size*8-8,z3.BitVecVal((dctx[0][current_load_addr]),8)) << (index*8))
            
            
            else:
                for r in self.memoryCache + self.codeCache:
                    if (current_load_addr >= r['start']) and (current_load_addr < (r['start'] + r['size'])):
                        i = (current_load_addr - r['start'])
                        value = ord(r['memory'][i : i+1])
                        load_value += (z3.ZeroExt(size*8-8,z3.BitVecVal(value,8)) << (index*8))
                        break
        
        opt = z3.Optimize()
        min = opt.minimize(load_value)
        max = opt.maximize(load_value)
        opt.set('priority', 'box')
        opt.check()
        min = min.value().as_long()
        max = max.value().as_long()
        return min,max
    
    def transform_z3_expr(self,z3_expr,All_infos,depth=1):
        
        
        sub_expr_names = get_z3_subexpressions_names(z3_expr)
        max_depth = depth 

        for sub_expr_name in sub_expr_names:
            if 'Load' in sub_expr_name:
                for i in range(len(All_infos)):
                    if All_infos[i][0] == sub_expr_name:
                        if All_infos[i][4]!=None:
                            old_load_expr = get_z3_expr_by_name(z3_expr,sub_expr_name)
                            new_load_expr,recursive_depth = self.transform_z3_expr(All_infos[i][4],All_infos,depth+1)
                            substitute_dict = [(old_load_expr,new_load_expr)]
                            z3_expr = z3.substitute(z3_expr,substitute_dict)

                            
                            if recursive_depth > max_depth:
                                max_depth = recursive_depth
                            break  
        return z3_expr,max_depth

    def solve_reg_expr(self,dataflowgraph,reg_str,reg_value,source_adr,target_adr,source_dctx):
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        
        reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_str)
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        
        
        
        
        
        tmp_result = solve_data_flow_exprs(reg_expr,reg_value,All_infos,source_dctx)
        
        result = {}
        for var in tmp_result:
            if "Load" in var:
                load_order = get_load_order(var,All_infos)
                result.update(solve_load_from_dctx(var,tmp_result[var],All_infos,source_dctx,result,load_order))
                result_hex = {}
                for addr in result:
                    
                    result_hex[hex(addr)] = hex(result[addr])   
        return result

    def solve_mem_expr(self,dataflowgraph,reg_str,size,mem_value,source_adr,target_adr,source_dctx):
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        
        
        scale_indexed_match = r'([\w]+)\+([\w]+)\*([\d]+)\+([\d]+)'
        
        base_indexed_match = r'([\w]+)\+([\w]+)\*([\d]+)'
        
        register_indirect_match = r'([\w]+)'

        matches=re.findall(scale_indexed_match,reg_str)
        if matches==[]:
            matches=re.findall(base_indexed_match,reg_str)
            if matches==[]:
                matches=re.findall(register_indirect_match,reg_str)

        if len(matches)<=1:
            reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,matches[0])
        else:
            reg1_expr,reg_load_infos1 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,matches[0])
            reg2_expr,reg_load_infos2 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,matches[1])
            reg_load_infos = reg_load_infos1 +reg_load_infos2
            reg_expr = reg1_expr + reg2_expr*matches[2]
            if len(matches)==4:
                reg_expr = reg_expr + matches[3]
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        
        addr_min,addr_max = evaluate_z3_expr_from_dctx(reg_expr,All_infos,source_dctx)
        
        mem_expr = None
        for i in range(len(All_infos)-1,-1,-1):
            if 'Store' in All_infos[i][0]:
                if (All_infos[i][5][0] == addr_min) and (All_infos[i][5][1] == addr_max):
                    mem_expr = All_infos[i][4]
                    break 
        result = {}
        if mem_expr!=None:
            
            tmp_result = solve_data_flow_exprs(mem_expr,mem_value,All_infos,source_dctx)
            
            for var in tmp_result:
                if 'Load' in var:
                    for i in range(len(All_infos)):
                        if All_infos[i][0] == var:
                            break
                    result[hex(All_infos[i][5][0])] = tmp_result[var]
                else:
                    result[var] = tmp_result[var]
        else:
            for i in range(size):
                result[hex(addr_min+i)] = (mem_value >> (i*8)) & 0xff
        return result

    
    def solve_load_from_dctx(self, Load_var,Load_value,All_infos,source_dctx,res,load_order):
        
        STle_addrs = []
        for i in range(len(All_infos)):
            if "Store" in All_infos[i][0]:
                STle_info = All_infos[i]
                start_addr = STle_info[5][0]
                
                if (STle_info[5][1]-STle_info[5][0]) == 0:
                    value_bytes = int(STle_info[4].size() / 8)
                    for j in range(value_bytes):
                        STle_addrs.append(start_addr+j)
        STle_addrs = list(set(STle_addrs))
        
        for i in range(len(load_order)-1,-1,-1):
            
            load_size = (self.get_size_from_load_name(All_infos[load_order[i][0]][0], self.gap_source_addrs, self.gap_target_addrs) // 8)
            if i == len(load_order)-1:
                if load_order[i][1] != None:
                    exit(-1)
                addr_expr = All_infos[load_order[i][0]][3]
                conditions = get_conditions_in_z3_expr(addr_expr,All_infos,source_dctx)
                opt = z3.Optimize()
                for condition in conditions:
                    opt.add(condition)
                min = opt.minimize(addr_expr)
                opt.set('priority', 'box')
                opt.check()
                min = min.value().as_long()
                
                if min not in res:
                    for addr in range(min, min + load_size):
                        res[addr] = 0
                    
                    if check_last_load_adr(load_order,i):
                        load_value = Load_value
                    else:
                        
                        gap_addr = calculate_gap_addr(All_infos,load_order,i)
                        load_value = obtain_load_addr(All_infos,source_dctx,res,STle_addrs,gap_addr)
                        if load_value == None:
                            exit(-1)
                else:
                    load_value = 0
                    for i in range(load_size):
                        load_value += res[min+i] << (i * 8)

                for i in range(load_size):
                    res[min + i] = (load_value >> (i * 8)) & 0xFF
                new_load_addr = load_value
            else:
                
                if load_order[i][1] == True:
                    addr_expr = All_infos[load_order[i][0]][3]
                    old_load_addr_expr = get_z3_expr_by_name(addr_expr,All_infos[load_order[i+1][0]][0])
                    substitute_dict = [(old_load_addr_expr,z3.BitVecVal(new_load_addr,old_load_addr_expr.size()))]
                    addr_expr = z3.substitute(addr_expr,substitute_dict)
                    conditions = get_conditions_in_z3_expr(addr_expr,All_infos,source_dctx)
                    opt = z3.Optimize()
                    for condition in conditions:
                        opt.add(condition)
                    min = opt.minimize(addr_expr)
                    opt.set('priority', 'box')
                    opt.check()
                    min = min.value().as_long()
                    if min not in res:
                        
                        for addr in range(min, min + load_size):
                            res[addr] = 0
                        
                        if check_last_load_adr(load_order, i):
                            load_value = Load_value
                        else:
                            
                            gap_addr = calculate_gap_addr(All_infos,load_order,i)
                            load_value = obtain_load_addr(All_infos,source_dctx,res,STle_addrs,gap_addr)
                            if load_value == None:
                                exit(-1)
                    else:
                        load_value = 0
                        for i in range(load_size):
                            load_value += res[min+i] << (i * 8)
                    
                    for i in range(load_size):
                        res[min + i] = (load_value >> (i * 8)) & 0xFF
                    new_load_addr = load_value
                else:
                    
                    continue
        return res

    def solve_mix_expr(self,target_block,dataflowgraph,path_constraint,regs_as_value,target_values,regs_as_addr,target_mems,source_adr,target_adr,target_count,source_dctx,DEBUG = True):
        
        result = {}
        
        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        self.gap_source_addrs = gap_source_addrs
        self.gap_target_addrs = gap_target_addrs
        
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        
        reg_expr_list = []
        reg_value_list = []
        reg_load_infos = []
        for i in range(len(regs_as_value)):
            reg_dic = regs_as_value[i]
            if type(reg_dic) == dict:
                reg_expr,reg_load_info = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['base'])
                if reg_dic['idx'] != None:
                    index_reg_expr, index_reg_load_info = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['idx'])
                    index_reg_expr = index_reg_expr * z3.BitVecVal(reg_dic['imm1'], index_reg_expr.size())
                    reg_load_info += index_reg_load_info
                    reg_expr += index_reg_expr 
                reg_expr += z3.BitVecVal(reg_dic['imm2'], reg_expr.size())
            elif type(reg_dic) == str:
                reg_expr,reg_load_info = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic)
            reg_expr_list.append(reg_expr)
            reg_value_list.append(target_values[i])
            reg_load_infos.extend(reg_load_info)
        
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        
        All_infos = Store_infos + reg_load_infos
        
        
        for i in range(len(regs_as_addr)):
            reg_dic = regs_as_addr[i]
            if type(reg_dic) == dict:
                reg_expr,reg_load_info = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['base'])
                if reg_dic['idx'] != None:
                    index_reg_expr, index_reg_load_info = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic['idx'])
                    index_reg_expr = index_reg_expr * z3.BitVecVal(reg_dic['imm1'], index_reg_expr.size())
                    reg_load_info += index_reg_load_info
                    reg_expr += index_reg_expr 
                reg_expr += z3.BitVecVal(reg_dic['imm2'], reg_expr.size())
            elif type(reg_dic) == str:
                reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_dic)
            
            All_infos.extend(reg_load_info)
            All_infos = remove_duplicates_by_first_element(All_infos)
            
            tmp_All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
            
            addr_min,addr_max = evaluate_z3_expr_from_dctx(reg_expr,tmp_All_infos,source_dctx)
            
            mem_expr = None
            for j in range(len(tmp_All_infos)-1,-1,-1):
                if 'Store' in tmp_All_infos[j][0]:
                    if (tmp_All_infos[j][5][0] == addr_min) and (tmp_All_infos[j][5][1] == addr_max):
                        mem_expr = tmp_All_infos[j][4]
                        break 
            if mem_expr!=None:
                
                reg_expr_list.append(mem_expr)
                reg_value_list.append(int(target_mems[i],16))
            else:
                target_mem = target_mems[i]
                size = int(len(target_mem)/2) - 1
                for j in range(size):
                    byte_value = int(target_mem[(2 + 2 * j):(4 + 2 * j)],16)
                    
                    result[addr_min+j] = byte_value

        
        
        conditional_jumps = control_flow_analyse.find_conditional_jumps(target_block, source_adr, target_adr, target_count)        
        operands_exprs_list,operands_Load_infos = path_constraint.get_z3_exprs_by_operands_list(source_adr, target_adr, dataflowgraph, self)
        path_constraint.operands_exprs_list = operands_exprs_list
        if len(conditional_jumps) != len(operands_exprs_list):
            print("The number of conditional jump instructions (%d) does not match the number of operand expressions (%d)"%(len(conditional_jumps),len(operands_exprs_list)))
            exit(-1)
        
        All_infos += operands_Load_infos
        All_infos = remove_duplicates_by_first_element(All_infos)
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        
        if DEBUG:
            self.add_ins_for_all_infos(All_infos,dataflowgraph,gap_source_addrs,gap_target_addrs)
        
        
        tmp_result = solve_data_exprs(reg_expr_list,reg_value_list,All_infos,source_dctx)      
        
        for var,var_value in tmp_result:
            if "Load" in var:
                load_order = get_load_order(var,All_infos)
                result.update(self.solve_load_from_dctx(var,var_value,All_infos,source_dctx,result,load_order))
        result_hex = {}
        for addr in result:
            
            result_hex[hex(addr)] = hex(result[addr])   
        return result