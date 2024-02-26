from triton import *
from . import build_dfgs
from . import generate_z3_exprs
from . import control_flow_analyse
import z3

jmp_code=['jnz','jz','jnc','jc','jo','je','jne','jcxz','jecxz','jrcxz','ja','jnbe','jae','jnb','jg','jnle','jge','jnl','jmp','jbe','ret','cmp']

class DataflowAnalysis():
    def __init__(self,ctx,pc,memoryCache,codeCache,plt_base_address,plt_size) -> None:
        self.target_block=[]  
        self.reg_range = {} 
        self.data_dependency = [] 
        self.dataflowgraph = build_dfgs.DataFlowGraph(plt_base_address,plt_size) 
        self.z3expr = generate_z3_exprs.Z3Eepr(memoryCache,codeCache) 
        self.path_constraint = control_flow_analyse.ControlFlowConstraint() 
        self.dctx = {} 
        
        self.dctx[pc] = [{},{},[],[]]
        for reg in ctx.getParentRegisters():
            value = ctx.getConcreteRegisterValue(reg)
            self.dctx[pc][1][reg.getName()] = value
        self.dctx[pc][2] = ctx.getTaintedMemory()
        for reg in ctx.getTaintedRegisters():
            self.dctx[pc][3].append(reg.getName())
        self.ctx = ctx

    
    def fresh(self,ctx,pc,memoryCache,codeCache,plt_base_address,plt_size):
        self.target_block=[]  
        self.reg_range = {} 
        self.data_dependency = [] 
        self.dataflowgraph = build_dfgs.DataFlowGraph() 
        self.z3expr = generate_z3_exprs.Z3Eepr(memoryCache,codeCache) 
        self.path_constraint = control_flow_analyse.ControlFlowConstraint() 
        self.dctx = {} 
        self.dctx[pc] = [{},{},[],[]]
        for reg in ctx.getParentRegisters():
            value = ctx.getConcreteRegisterValue(reg)
            self.dctx[pc][1][reg.getName()] = value
        self.dctx[pc][2] = ctx.getTaintedMemory()
        for reg in ctx.getTaintedRegisters():
            self.dctx[pc][3].append(reg.getName())
        self.ctx = ctx

    def collect_opcode(self, instruction,hooking_flag):
        
        pc = instruction.getAddress() 
        opcode = instruction.getOpcode() 
        
        self.target_block.append((pc,opcode,instruction,hooking_flag))
        
    
    def get_memory_overlaps(self, Cache, start, end, flag):
        
        overlaps = []
        for block in Cache:
            
            if block['start'] < end and block['start'] + block['size'] > start:
                
                overlap_start = max(block['start'], start)
                overlap_end = min(block['start'] + block['size'], end)
                overlap_size = overlap_end - overlap_start
                permissons = block['permissions']
                
                if flag in permissons:
                    overlaps.append({
                        'start': overlap_start,
                        'size': overlap_size,
                        'permissions': permissons,
                    })
        return overlaps
    
    def get_reg_range_in_dfgs(self,source_adr,target_adr,target_count,reg_str):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        if not (source_adr in self.z3expr.reg_expr and target_adr in self.z3expr.reg_expr[source_adr] and reg_str in self.z3expr.reg_expr[source_adr][target_adr]):
            min,max = self.z3expr.get_reg_range_by_vsa(self.dataflowgraph,source_adr,target_adr,reg_str,source_dctx)
        return min,max
    
    def get_mix_range_in_dfgs(self,source_adr,target_adr,target_count,reg_str):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        if not (source_adr in self.z3expr.reg_expr and target_adr in self.z3expr.reg_expr[source_adr] and reg_str in self.z3expr.reg_expr[source_adr][target_adr]):
            min,max = self.z3expr.get_mix_range_by_vsa(self.target_block, self.dataflowgraph, self.path_constraint, source_adr, target_adr, target_count, reg_str, source_dctx)
        return min,max
    
    def get_expr_range_in_dfgs(self,source_adr,target_adr,target_count,reg_dic):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        
        min,max = self.z3expr.get_expr_range_by_vsa(self.target_block, self.dataflowgraph, self.path_constraint, source_adr, target_adr, target_count, reg_dic, source_dctx)
        return min,max
    
    def check_data_dependency(self,source_adr,target1_adr,reg1_dic,target2_adr,reg2_dic):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target1_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target1_adr,1)
        if not (source_adr in self.dataflowgraph.gap_addrs and target2_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target2_adr,1)
        
        if not (source_adr in self.z3expr.reg_expr and target1_adr in self.z3expr.reg_expr[source_adr] and reg1_dic in self.z3expr.reg_expr[source_adr][target1_adr]):
            if self.z3expr.check_data_dependency_by_vsa(self.dataflowgraph,source_adr,target1_adr,reg1_dic,target2_adr,reg2_dic,source_dctx):
                return True
            else:
                return False

    def save_dctx(self,source_adr,target_adr,target_count,source_dctx,ctx):
            
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count)
        
        gap_source_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][1]
        for i in range(len(gap_source_addrs)):
            self.z3expr.vex_to_z3_in_dfg(self.dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],self.dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
        Store_infos,Load_infos = self.z3expr.get_stle_exprs_in_dfgs(self.dataflowgraph.irsb_list,gap_source_addrs,gap_target_addrs)
        All_infos = sorted(Store_infos + Load_infos,key=lambda x: (x[1], x[2]))
          
        All_infos = self.z3expr.addr_and_value_set_analyse(All_infos,source_dctx,gap_source_addrs,gap_target_addrs)

        self.dctx[target_adr] = [{},{},[],[]]
        for i in range(len(All_infos)):
            if 'Store' in All_infos[i][0]:
                store_addr = All_infos[i][5][0]
                store_value = All_infos[i][6][0]
                store_value_size = int(All_infos[i][4].size() / 8)
                for index in range(store_value_size):
                    current_store_addr = store_addr + index
                    current_store_value = (store_value >> (index * 8)) & 0xFF
                    self.dctx[target_adr][0][current_store_addr] = current_store_value
        
        for reg in ctx.getParentRegisters():
            value = ctx.getConcreteRegisterValue(reg)
            self.dctx[target_adr][1][reg.getName()] = value
        
        self.dctx[target_adr][2] = ctx.getTaintedMemory()

        regs = ctx.getTaintedRegisters()
        for reg in regs:
            self.dctx[target_adr][3].append(reg.getName())
        self.dctx[target_adr][3] = []

    def get_origin_mem_by_reg_expr(self,reg_str,reg_value,source_adr,target_adr,target_count):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        result = self.z3expr.solve_reg_expr(self.dataflowgraph,reg_str,reg_value,source_adr,target_adr,source_dctx)
        
        result_hex = {}
        for addr in result:
            if addr in source_dctx[2]:
                result_hex[hex(addr)] = hex(result[addr])
        return result_hex

    def get_origin_mem_by_addr_expr(self,addr_expr_str,size,mem_value,source_adr,target_adr,target_count):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        result = self.z3expr.solve_mem_expr(self.dataflowgraph,addr_expr_str,size,mem_value,source_adr,target_adr,source_dctx)
        return result
    
    def get_origin_mem_by_control_expr(self,source_adr,target_adr,target_count):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count)
        
        gap_source_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][1]
        for i in range(len(gap_source_addrs)):
            if not (gap_source_addrs[i] in self.z3expr.z3_vars and gap_target_addrs[i] in self.z3expr.z3_vars[gap_source_addrs[i]]):
                self.z3expr.vex_to_z3_in_dfg(self.dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],\
                    self.dataflowgraph.irsb_list[gap_source_addrs[i]][gap_target_addrs[i]],\
                        gap_source_addrs[i],gap_target_addrs[i])
        
        result = self.path_constraint.get_control_flow_payload(source_adr, target_adr, target_count, self.target_block, self.dataflowgraph, self.z3expr, source_dctx)
        
        result_hex = {}
        for addr in result:
            if addr in source_dctx[2]:
                result_hex[hex(addr)] = hex(result[addr])
        return result_hex
    
    def get_origin_mem(self,reg_str,reg_value,source_adr,target_adr,target_count):
        
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        result = self.z3expr.solve_mix_expr(self.target_block,self.dataflowgraph,self.path_constraint,reg_str,reg_value,source_adr,target_adr,target_count,source_dctx)
        
        result_hex = {}
        for addr in result:
            if addr in source_dctx[2]:
                result_hex[hex(addr)] = hex(result[addr])
        return result_hex

    def get_origin_mem_by_mix_expr(self,regs_as_value,target_values,regs_as_addr,target_mems,source_adr,target_adr,target_count):
        
        if regs_as_value == [] and regs_as_addr == []:
            return {}
        source_dctx = self.dctx[source_adr]
        
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        
        result = self.z3expr.solve_mix_expr(self.target_block,self.dataflowgraph,self.path_constraint,\
            regs_as_value,target_values,regs_as_addr,target_mems, \
                source_adr,target_adr,target_count,source_dctx)
        
        result_hex = {}

        for addr in result:
            if addr in source_dctx[2]:
                result_hex[hex(addr)] = hex(result[addr])

        return result_hex