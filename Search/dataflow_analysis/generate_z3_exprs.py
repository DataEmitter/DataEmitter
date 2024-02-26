import z3
import networkx as nx
import archinfo
import re
from triton import *
import threading

regs_list = ['rax','rbx','rcx','rdx','rsi','rdi','rbp','rsp','rip','r8','r9','r10','r11','r12','r13','r14','r15','eflags']

def get_register_name(arch, offset):
    for key in arch.register_list:
        reg_offset=arch.get_register_offset(key.name)
        if offset == reg_offset:
            return key.name

def calculate_depths(graph):
    # Perform topological sort of the graph
    topo_order = list(nx.topological_sort(graph))

    # Create a dictionary to store the depth of each node
    depths = {node: 0 for node in topo_order}

    # Iterate through the nodes in topological order, updating their depths
    for node in topo_order:
        # Get the maximum depth of the node's incoming edges
        max_depth = 0
        for pred in graph.predecessors(node):
            max_depth = max(max_depth, depths[pred])
        
        # Update the depth of the node
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
    # pattern = r'Load_(t\d+)(?!_)'
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
        else:
            for child in expr.children():
                helper(child)

    helper(expr)

    return names

def get_conditions_in_z3_expr(z3_expr,All_infos,source_dctx):

    # 获得z3表达式中所有寄存器变量和Load变量
    sub_expr_names = get_z3_subexpressions_names(z3_expr)
    # 收集各变量的约束条件
    conditions = []
    for sub_expr_name in sub_expr_names:
        if sub_expr_name in regs_list:
            sub_reg_expr = get_z3_expr_by_name(z3_expr,sub_expr_name)
            # 对于寄存器，我们直接取source_dctx中的值作为其最小值和最大值（通常认为寄存器不会被污点标记）
            value = source_dctx[1][sub_expr_name]
            z3_value = z3.BitVecVal(value,sub_reg_expr.size())
            conditions.append(z3.ULE(sub_reg_expr,z3_value))
            conditions.append(z3.UGE(sub_reg_expr,z3_value))
        elif 'Load' in sub_expr_name:
            # 查找该Load变量在load_infos中的信息
            sub_load_expr = get_z3_expr_by_name(z3_expr,sub_expr_name)
            for i in range(len(All_infos)):
                if All_infos[i][0] == sub_expr_name:
                    # 直接取出对应的值表达式的范围
                    min_value = All_infos[i][6][0]
                    max_value = All_infos[i][6][1]
                    z3_min_value = z3.BitVecVal(min_value,sub_load_expr.size())
                    z3_max_value = z3.BitVecVal(max_value,sub_load_expr.size())
                    conditions.append(z3.ULE(sub_load_expr,z3_max_value))
                    conditions.append(z3.UGE(sub_load_expr,z3_min_value))
                    break
    return conditions

def evaluate_z3_expr_from_dctx(z3_expr,All_infos,source_dctx):

    # 获得z3表达式中所有变量的约束条件
    conditions = get_conditions_in_z3_expr(z3_expr,All_infos,source_dctx)
    # 利用z3的Optimize类求解范围
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

def check_z3_expr_from_dctx(reg1_expr,All_infos1,reg2_expr,All_infos2,source_dctx):

    # 获得寄存器1表达式中所有变量的约束条件
    conditions1 = get_conditions_in_z3_expr(reg1_expr,All_infos1,source_dctx)
    
    # 获得寄存器2表达式中所有变量的约束条件
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

def solve_z3_expr_from_dctx(reg_expr,reg_value,All_infos,source_dctx):
    conditions = get_conditions_in_z3_expr(reg_expr,All_infos,source_dctx)
    solver = z3.Solver()
    reg_value = z3.BitVecVal(reg_value,reg_expr.size())
    solver.add(reg_expr == reg_value)
    for condition in conditions:
        solver.add(condition)
    res = {}
    if solver.check()==z3.sat:
        print("有解:")
        m = solver.model()
        for v in m:
            res[str(v)] = m[v].as_long()
    else:
        print("无解")
    return res


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
        print("VEX IR:%s 中操作数的向量位数不对"%stmt)
        print("操作数位数：%d"%(operand.size()))
        exit(-1)
    gap_size = size2 - size1
    # Widening conversions
    if "Uto" in stmt.data.op:
        rvalue=z3.ZeroExt(gap_size,operand)
    elif "Sto" in stmt.data.op:
        rvalue=z3.SignExt(gap_size,operand)
    # Narrow conversions
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
        print("VEX IR:%s 中操作数的向量位数不对"%stmt)
        print("操作数1位数: %d"%(rvalue1.size()))
        print("操作数2位数: %d"%(rvalue2.size()))
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
        print("VEX IR:%s 中存在未处理的cmp类型"%stmt)
        exit(-1)
    return rvalue


class Z3Eepr():
    def __init__(self,memoryCache,codeCache) -> None:
        self.z3_vars={} # 数据流图中对应的所有IR变量的z3表达式
        self.z3_var_to_stmt = {} # 数据流图中对应的变量到VEX IR Stmt的映射
        self.z3_store_value_vars = {} # 数据流图中对应的STle变量的z3值表达式
        self.z3_store_addr_vars = {} # 数据流图中对应的STle变量的z3地址表达式
        self.reg_expr = {} # 数据流分析中终点寄存器相对于起点的表达式
        self.memoryCache = memoryCache
        self.codeCache = codeCache
    # 每一次路径探索时重置
    def fresh(self,memoryCache,codeCache):
        self.z3_vars={} # 数据流图中对应的所有IR变量的z3表达式
        self.z3_var_to_stmt = {} # 数据流图中对应的变量到VEX IR Stmt的映射
        self.z3_store_value_vars = {} # 数据流图中对应的STle变量的z3值表达式
        self.z3_store_addr_vars = {} # 数据流图中对应的STle变量的z3地址表达式
        self.reg_expr = {} # 数据流分析中终点寄存器相对于起点的表达式
        self.memoryCache = memoryCache
        self.codeCache = codeCache
    
    def vex_to_z3_in_dfg(self,dfg,source_adr,target_adr):
        '''
        将vex节点转换为z3表达式(基于数据流图来做)
        args:
            dfg:DiGraph,数据流图
            source_adr:dfg的起点
            target_adr:dfg的终点
        return:
            [],z3表达式列表
        note:
            采用广度优先遍历算法(多个起点，一个终点，正向遍历)
        '''
        # 得到各个节点的深度，以target_node作为深度为1的节点,其他节点的深度为到达target的最大深度
        # dfg = dfgs[source_adr][target_adr]
        reverse_depths = calculate_depths(dfg.reverse())
        depths = {} # 各个深度对应的节点
        max_depth = 0 # 最大深度
        for node in reverse_depths:
            depth = reverse_depths[node]
            if depth not in depths:
                depths[depth] = [node]
            else:
                depths[depth].append(node)
            if depth > max_depth:
                max_depth = depth
        z3_vars = {} # 变量名->z3表达式 变量名包括t1,t2,rax1,rax2... 
        z3_var_to_stmt = {} # 变量名->vex ir stmt
        z3_store_value_vars = {} # STle变量名->值表达式
        z3_store_addr_vars = {} # STle变量名->地址表达式
        maps = {} # vex node -> 寄存器名

        current_depth=max_depth
        # 开始遍历图
        while current_depth>0:
            # 从队列中取出一个节点
            for node in depths[current_depth]:  
                # 开始对节点进行分析，将其转换为z3表达式
                stmt = node
                rvalue = None # 每次分析节点时重置rvalue的z3表达式
                # 当前节点是常量节点，直接跳过，不产生z3变量和表达式
                if stmt.tag != 'Iex_Const':
                    exprs = list(stmt.expressions)
                    # print(stmt)
                    if stmt.tag == 'Ist_WrTmp': # 目的操作数为tmp
                        if exprs[0].tag == 'Iex_Binop': # 二元操作
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
                            # 对于双操作数运算，需要位数对齐
                            if rvalue2.size()<rvalue1.size():
                                rvalue2 = z3.ZeroExt((rvalue1.size())-(rvalue2.size()),rvalue2)
                            if rvalue1.size()<rvalue2.size():
                                rvalue1 = z3.ZeroExt((rvalue2.size())-(rvalue1.size()),rvalue1)
                            # 根据vex ir的二元操作类型做不同操作
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
                            # 暂时不分析Cmp类型指令
                            elif 'Cmp' in stmt.data.op:
                                rvalue = (handle_cmp(rvalue1,rvalue2,stmt))

                        elif exprs[0].tag == 'Iex_Unop': # 一元操作
                            if exprs[1].tag == 'Iex_RdTmp':
                                operand = z3_vars[f"t{exprs[1].tmp}"]
                            else:
                                operand = exprs[1].con.value
                                size = exprs[1].constants[0].size
                                operand = z3.BitVecVal(operand, size) 
                            # 根据vex ir的一元操作类型获得对应的z3表达式
                            # 转换
                            if "to" in stmt.data.op:
                                rvalue = handle_conversions(operand,stmt)
                            # 按位取反
                            elif "Not" in stmt.data.op:
                                rvalue = ~operand
                            # 取负数
                            elif "Neg" in stmt.data.op:
                                rvalue = z3.BitVecNeg(operand)
                        
                        elif exprs[0].tag == 'Iex_RdTmp': # 读取临时变量的值
                            operand = z3_vars[f"t{exprs[0].tmp}"]
                            rvalue = operand
                            
                        elif exprs[0].tag == 'Iex_Const': # 读取常量
                            rvalue = exprs[0].con.value
                            size = exprs[0].constants[0].size
                            rvalue = z3.BitVecVal(rvalue, size)

                        elif exprs[0].tag == 'Iex_Get': # get操作
                            #offset = exprs[0].offset # 寄存器偏移
                            #reg_name=get_register_name(archinfo.ArchAMD64(),offset)
                            offset = exprs[0].offset # 寄存器偏移
                            reg_name=get_register_name(archinfo.ArchAMD64(),offset) # 寄存器名称
                            type = exprs[0].ty
                            pattern = r'Ity_I(\d+)'
                            match = re.search(pattern,type)
                            size = int(match.group(1))
                            pre_nodes=list(dfg.predecessors(node)) # get操作的父节点
                            if len(pre_nodes)==0: # 该情况下寄存器就是分析起点的状态
                                z3_vars[reg_name]=z3.BitVec(reg_name,size) # 创建原始寄存器变量
                                z3_var_to_stmt[reg_name] = stmt # 进行映射
                                maps[node]= reg_name 
                            else:
                                pre_node = pre_nodes[0]
                                reg_name = maps[pre_node]  # 获得寄存器的名称
                            rvalue = z3.Extract(size-1, 0, z3_vars[reg_name])

                        elif exprs[0].tag == 'Iex_Load':
                            type = exprs[0].ty
                            pattern = r'Ity_I(\d+)'
                            match = re.search(pattern,type)
                            size = int(match.group(1)) # 确定新创建load变量的大小
                            if exprs[1].tag == 'Iex_RdTmp':
                                var_name = "Load_"+f"t{exprs[1].tmp}"
                            else:
                                var_name = "Load_"+str(exprs[1].con.value)
                            z3_vars[var_name] = z3.BitVec(var_name,size) # 对于load操作，初始化一个新的变量
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
                            print("VEX IR:%s 转化z3表达式失败"%stmt)
                            exit(-1)
                        lvalue_name = f"t{stmt.tmp}"
                        z3_vars[lvalue_name] = rvalue
                        z3_var_to_stmt[lvalue_name] = stmt

                    elif stmt.tag == 'Ist_Store': # 将数据存储到内存中
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
                            print("VEX IR:%s 转化z3表达式失败"%stmt)
                            exit(-1)
                        z3_vars[var_name]= rvalue
                        z3_var_to_stmt[var_name] = stmt
                        z3_store_value_vars[var_name]=rvalue 
                        z3_store_addr_vars[var_name]=z3_vars[f"t{exprs[0].tmp}"]

                    elif stmt.tag == 'Ist_Put': # 给寄存器赋值
                        offset = stmt.offset # 寄存器偏移
                        reg_name=get_register_name(archinfo.ArchAMD64(),offset) # 寄存器名称
                        new_reg_name=rename_reg(reg_name,z3_vars) # 带版本号的寄存器名称
                        if exprs[0].tag == 'Iex_RdTmp':
                            rvalue = z3_vars[f"t{exprs[0].tmp}"]
                        elif exprs[0].tag == 'Iex_Const':
                            rvalue = exprs[0].con.value
                            size = exprs[0].con.size
                            rvalue = z3.BitVecVal(rvalue, size)
                        
                        if rvalue == None:
                            print("VEX IR:%s 转化z3表达式失败"%stmt)
                            exit(-1)
                        z3_vars[new_reg_name]= rvalue
                        z3_var_to_stmt[new_reg_name] = stmt
                        maps[node]=new_reg_name
                
            current_depth-=1 

        # 获得DFG对应所有变量的z3表达式
        for var in z3_vars:
            z3_vars[var] = z3.simplify(z3_vars[var])
        if source_adr not in self.z3_vars.keys():
            self.z3_vars[source_adr]={}
        self.z3_vars[source_adr][target_adr]=z3_vars

        # 获得DFG对应变量->ir stmt的映射
        if source_adr not in self.z3_var_to_stmt.keys():
            self.z3_var_to_stmt[source_adr]={}
        self.z3_var_to_stmt[source_adr][target_adr]=z3_var_to_stmt

        # 获得DFG中所有STle变量的值表达式
        for store_var in z3_store_value_vars:
            z3_store_value_vars[store_var] = z3.simplify(z3_store_value_vars[store_var])
        if source_adr not in self.z3_store_value_vars.keys():
            self.z3_store_value_vars[source_adr]={}
        self.z3_store_value_vars[source_adr][target_adr]=z3_store_value_vars
        
        # 获得DFG中所有STle变量的地址表达式
        for store_var in z3_store_addr_vars:
            z3_store_addr_vars[store_var] = z3.simplify(z3_store_addr_vars[store_var])
        if source_adr not in self.z3_store_addr_vars.keys():
            self.z3_store_addr_vars[source_adr]={}
        self.z3_store_addr_vars[source_adr][target_adr]=z3_store_addr_vars

    def resolve_load_variables(self, source_addr, target_addr, expr):
        '''
        递归解析load变量中的load变量
        args:
            source_addr: 起始地址
            target_addr: 终点地址
            exprs: 待解析的表达式
        return:
            resolved_load_exprs: 解析后的load变量对应地址变量表达式字典
        '''
        resolved_load_exprs = {}

        # 获取load变量对应的地址变量
        load_vars = find_load_addr_vars(expr)
        if load_vars is not None:
            # 解析load变量中的load变量
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

    def get_reg_exprs(self, irsb_list, source_adr, target_adr, reg_str):
        location = -1
        flag = 0
        z3_vars = self.z3_vars[source_adr][target_adr]
        # 创建一个值为0，位数为64的位向量
        reg_z3_expr = z3.BitVecVal(0,64)
        for var in z3_vars:
            if reg_str in var:
                stmt = self.z3_var_to_stmt[source_adr][target_adr][var]
                # print(stmt)
                index = irsb_list[source_adr][target_adr].index(str(stmt))
                if index > location:
                    location = index
                    flag = 1
                    var_size = z3_vars[var].size()
                    if var_size < 64:
                        reg_z3_expr = z3.Extract(63,var_size,reg_z3_expr) << var_size + z3_vars[var]
                    else:
                        reg_z3_expr = z3_vars[var]

        if flag == 0:
            reg_z3_expr = z3.BitVec(reg_str,64)
        return reg_z3_expr
    
    def get_reg_exprs_in_dfgs(self,irsb_list,gap_source_addrs,gap_target_addrs,reg_str):

        result_load_exprs = {} # 记录每一个阶段dfg中出现的load变量的地址变量及其表达式
        result_Load_infos = [] # 记录每一个阶段dfg中出现的load变量的信息(包括其在dfg中的位置和地址表达式)
        relied_reg_vars = [] # 寄存器变量名
        for i in range(len(gap_source_addrs)-1,-1,-1):
            update_exprs = [] # 当前dfg替换的表达式
            if i == len(gap_source_addrs)-1:
                result_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                update_exprs.append(result_expr)
                result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
            else:
                # 替换寄存器变量
                for reg_str in relied_reg_vars:
                    new_reg_expr = self.get_reg_exprs(irsb_list,gap_source_addrs[i],gap_target_addrs[i],reg_str)
                    var_name = reg_str
                    result_expr = z3.simplify(result_expr)
                    reg_expr = get_z3_expr_by_name(result_expr,var_name)
                    substitute_dict = [(reg_expr,new_reg_expr)]
                    result_expr = z3.substitute(result_expr,substitute_dict)
                    update_exprs.append(new_reg_expr)
                    result_expr = self.rename_load_vars(result_expr,gap_source_addrs[i],gap_target_addrs[i],i)
                # 替换load变量对应的地址变量
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
                        # 更新改变后的表达式名字
                        result_load_exprs[result_load_addr_var] = self.rename_load_vars(result_load_exprs[result_load_addr_var],gap_source_addrs[i],gap_target_addrs[i],i)
                        update_exprs.append(new_reg_expr)
                        #result_expr = self.rename_load_vars(result_load_exprs[result_load_addr_var],gap_source_addrs[i],gap_target_addrs[i],i)

            # 保存当前表达式依赖的寄存器变量
            relied_reg_vars = find_relied_reg_vars(result_expr)
            # 重命名load变量，不同阶段dfg的load变量可能出现同名情况
            relied_load_exprs = {} # load变量对应的地址变量名：地址变量的表达式 
            new_relied_load_exprs = {}
            for update_expr in update_exprs:
                relied_load_exprs.update(self.resolve_load_variables(gap_source_addrs[i],gap_target_addrs[i],update_expr))
            for relied_load_var in relied_load_exprs:
                new_relied_load_exprs[relied_load_var + '_' + str(i)] = self.rename_load_vars(relied_load_exprs[relied_load_var],gap_source_addrs[i],gap_target_addrs[i],i)
            result_load_exprs.update(new_relied_load_exprs)
        
        # 简化表达式
        result_expr = z3.simplify(result_expr)
        for result_load_addr_var in result_load_exprs:
            result_load_exprs[result_load_addr_var] = z3.simplify(result_load_exprs[result_load_addr_var])

        # 归纳所有Load变量的信息
        for result_load_addr_var in result_load_exprs:
            result_load_var = 'Load_' + result_load_addr_var
            dfg_pos,ir_pos = find_position_by_name(irsb_list,gap_source_addrs,gap_target_addrs,result_load_var)
            result_Load_infos.append([result_load_var,dfg_pos,ir_pos,result_load_exprs[result_load_addr_var]])

        return result_expr,result_Load_infos

    def get_reg_range_by_vsa(self,dataflowgraph,source_adr,target_adr,reg_str,source_dctx):

        gap_source_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = dataflowgraph.gap_addrs[source_adr][target_adr][1]
        # 分区间转化vex ir得到z3表达式
        for i in range(len(gap_source_addrs)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])

        # 递归替换各区间表达式得到寄存器的最终表达式
        reg_expr,reg_load_infos = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs,reg_str)
        # 获取分析起点到分析终点所有对内存的修改信息
        Store_infos,Load_infos = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        # 合并reg_load_infos和Load_infos并去除重复元素
        reg_load_infos = remove_duplicates_by_first_element(reg_load_infos + Load_infos)
        # 合并reg_load_infos和Store_infos
        All_infos = Store_infos + reg_load_infos
        # 对每个Load变量和Store变量进行值集分析，获取对应的地址和值的表达式范围
        All_infos = self.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)
        # 解析reg_expr得到其范围
        min,max = evaluate_z3_expr_from_dctx(reg_expr,All_infos,source_dctx)
        return min,max
    
    def check_data_dependency_by_vsa(self,dataflowgraph,source_adr,target1_adr,reg1_str,target2_adr,reg2_str,source_dctx):

        gap_source_addrs1 = dataflowgraph.gap_addrs[source_adr][target1_adr][0]
        gap_target_addrs1 = dataflowgraph.gap_addrs[source_adr][target1_adr][1]
        # 分区间转化vex ir得到z3表达式
        for i in range(len(gap_source_addrs1)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs1[i]][gap_target_addrs1[i]],gap_source_addrs1[i],gap_target_addrs1[i])
        # 递归替换各区间表达式得到寄存器的最终表达式
        reg1_expr,reg_load_infos1 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1,reg1_str)
        # 获取分析起点到分析终点所有对内存的修改信息
        Store_infos1,Load_infos1 = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs1,gap_target_addrs1)
        # 合并reg_load_infos和Load_infos并去除重复元素
        reg_load_infos1 = remove_duplicates_by_first_element(reg_load_infos1 + Load_infos1)
        # 合并reg_load_infos和Store_infos
        All_infos1 = Store_infos1 + reg_load_infos1
        # 对每个Load变量和Store变量进行值集分析，获取对应的地址和值的表达式范围
        All_infos1 = self.addr_and_value_set_analyse(All_infos1,source_dctx,gap_source_addrs1,gap_target_addrs1)
        
        gap_source_addrs2 = dataflowgraph.gap_addrs[source_adr][target2_adr][0]
        gap_target_addrs2 = dataflowgraph.gap_addrs[source_adr][target2_adr][1]
        # 分区间转化vex ir得到z3表达式
        for i in range(len(gap_source_addrs2)):
            self.vex_to_z3_in_dfg(dataflowgraph.dfgs[gap_source_addrs2[i]][gap_target_addrs2[i]],gap_source_addrs2[i],gap_target_addrs2[i])
        # 递归替换各区间表达式得到寄存器的最终表达式
        reg2_expr,reg_load_infos2 = self.get_reg_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2,reg2_str)
        # 获取分析起点到分析终点所有对内存的修改信息
        Store_infos2,Load_infos2 = self.get_stle_exprs_in_dfgs(dataflowgraph.irsb_list,gap_source_addrs2,gap_target_addrs2)
        # 合并reg_load_infos和Load_infos并去除重复元素
        reg_load_infos2 = remove_duplicates_by_first_element(reg_load_infos2 + Load_infos2)
        # 合并reg_load_infos和Store_infos
        All_infos2 = Store_infos2 + reg_load_infos2
        # 对每个Load变量和Store变量进行值集分析，获取对应的地址和值的表达式范围
        All_infos2 = self.addr_and_value_set_analyse(All_infos2,source_dctx,gap_source_addrs2,gap_target_addrs2)
        # 判断reg1_expr==reg2_expr是否有解
        if check_z3_expr_from_dctx(reg1_expr,All_infos1,reg2_expr,All_infos2,source_dctx):
            return True
        else:
            return False

    def addr_and_value_set_analyse(self,All_infos,source_dctx,gap_source_addrs,gap_target_addrs):

        # 在值集分析前，将个load变量的值表达式置为None
        for i in range(len(All_infos)):
            if 'Load' in All_infos[i][0]:
                All_infos[i].append(None)

        All_infos = sorted(All_infos,key=lambda x: (x[1], x[2]))
        for i in range(len(All_infos)):
            var_name = All_infos[i][0]
            if 'Store' in var_name:
                # 首先分析Store变量的地址表达式范围
                addr_expr = All_infos[i][3]
                addr_min,addr_max = evaluate_z3_expr_from_dctx(addr_expr,All_infos,source_dctx)
                All_infos[i].append((addr_min,addr_max))
                # 接着分析Store变量的值表达式范围
                value_expr = All_infos[i][4]
                value_min,value_max = evaluate_z3_expr_from_dctx(value_expr,All_infos,source_dctx)
                All_infos[i].append((value_min,value_max))
            elif 'Load' in var_name:
                # 首先分析Load变量的地址表达式范围
                addr_expr = All_infos[i][3]
                addr_min,addr_max = evaluate_z3_expr_from_dctx(addr_expr,All_infos,source_dctx)
                All_infos[i].append((addr_min,addr_max))
                # 根据地址范围寻找前面是否有相同地址范围的Store变量
                flag = 0 # 标记是否找到相同地址范围的Store变量
                for j in range(i,-1,-1):
                    if 'Store' in All_infos[j][0]:
                        if All_infos[j][5][0] == All_infos[i][5][0] and All_infos[j][5][1] == All_infos[i][5][1]:
                            # 更新All_infos[i]的值表达式
                            All_infos[i][4] = All_infos[j][4]
                            # 获取All_infos[i]的值表达式范围
                            All_infos[i].append((All_infos[j][6][0],All_infos[j][6][1]))
                            flag = 1
                            break
                # 如果没有找到,相同地址范围的Store变量，则根据地址范围和source_dctx得到值表达式范围
                if flag == 0:
                    # 根据Load变量名称得到向量位数
                    if (addr_max - addr_min) > 10000:
                        print("出现地址遍历爆炸问题")
                        exit(0)
                    size = self.get_size_from_load_name(All_infos[i][0],gap_source_addrs,gap_target_addrs)
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
            # 地址在对应的dctx污染内存中
            if current_load_addr in dctx[2]:
                tainted_var = z3.BitVec(str(current_load_addr),8)
                load_value += (z3.ZeroExt(size*8-8,tainted_var) << (index*8))

            # 地址在对应的dctx中的内存修改中
            elif current_load_addr in dctx[0]:
                load_value += (z3.ZeroExt(size*8-8,z3.BitVecVal((dctx[0][current_load_addr]),8)) << (index*8))
            
            # 地址在dump对应的内容中
            else:
                for r in self.memoryCache + self.codeCache:
                    if current_load_addr >= r['start'] and current_load_addr < r['start'] + r['size']:
                        i = (current_load_addr - r['start'])
                        value = ord(r['memory'][i : i+1])
                        load_value += (z3.ZeroExt(size*8-8,z3.BitVecVal(value,8)) << (index*8))
        
        opt = z3.Optimize()
        min = opt.minimize(load_value)
        max = opt.maximize(load_value)
        opt.set('priority', 'box')
        opt.check()
        min = min.value().as_long()
        max = max.value().as_long()
        return min,max
        
    def z3_solve(self,equations,variables):

        s = z3.Solver()
        s.add(equations + variables)
        res = {}
        if s.check()==z3.sat:
            print("有解:")
            m = s.model()
            for v in m:
                res[str(v)] = m[v].as_long()
        else:
            print("无解")
        return res
    
   