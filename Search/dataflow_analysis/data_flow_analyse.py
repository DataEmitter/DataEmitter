from triton import *
from . import build_dfgs
from . import generate_z3_exprs
import z3

jmp_code=['jnz','jz','jnc','jc','jo','je','jne','jcxz','jecxz','jrcxz','ja','jnbe','jae','jnb','jg','jnle','jge','jnl','jmp','jbe','ret','cmp']

class DataflowAnalysis():
    def __init__(self,ctx,pc,memoryCache,codeCache) -> None:
        self.target_block=[]  # 各条指令对应的opcode
        self.reg_range = {} # 数据流分析中终点寄存器相对于起点的表达式范围
        self.data_dependency = [] # 存在数据流依赖关系的指令
        self.dataflowgraph = build_dfgs.DataFlowGraph() # 初始化数据流图
        self.z3expr = generate_z3_exprs.Z3Eepr(memoryCache,codeCache) # 初始化z3表达式
        self.dctx = {} # 初始化数据流分析的各个目标位置的状态(相对dump文件修改的内存和寄存器,符号化寄存器和内存状态)
        # 根据初始状态的ctx初始化一个dctx
        self.dctx[pc] = [{},{},[],[]]
        for reg in ctx.getParentRegisters():
            value = ctx.getConcreteRegisterValue(reg)
            self.dctx[pc][1][reg.getName()] = value
        self.dctx[pc][2] = ctx.getTaintedMemory()
        for reg in ctx.getTaintedRegisters():
            self.dctx[pc][3].append(reg.getName())
        self.ctx = ctx

    # 每一次路径探索时重置
    def fresh(self,ctx,pc,memoryCache,codeCache):
        self.target_block=[]  # 各条指令对应的opcode
        self.reg_range = {} # 数据流分析中终点寄存器相对于起点的表达式范围
        self.data_dependency = [] # 存在数据流依赖关系的指令
        self.dataflowgraph = build_dfgs.DataFlowGraph() # 初始化数据流图
        self.z3expr = generate_z3_exprs.Z3Eepr(memoryCache,codeCache) # 初始化z3表达式
        self.dctx = {} # 初始化数据流分析的各个目标位置的状态(相对dump文件修改的内存和寄存器,符号化寄存器和内存状态)
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
        # collect the opcode
        self.target_block.append((pc,opcode,instruction,hooking_flag))
    
    def get_memory_overlaps(self, Cache, start, end, flag):
        overlaps = []
        for block in Cache:
            # Check if the block overlaps with the given range
            if block['start'] < end and block['start'] + block['size'] > start:
                # Calculate the overlap between the block and the given range
                overlap_start = max(block['start'], start)
                overlap_end = min(block['start'] + block['size'], end)
                overlap_size = overlap_end - overlap_start
                permissons = block['permissions']
                # Add the overlap to the list
                if flag in permissons:
                    overlaps.append({
                        'start': overlap_start,
                        'size': overlap_size,
                        'permissions': permissons,
                    })
        return overlaps
    
    def get_reg_range_in_dfgs(self,source_adr,target_adr,target_count,reg_str):
        '''
        获取寄存器的取值范围
        args:
            source_adr:int,数据流分析的起点
            target_adr:int,数据流分析的终点
            target_count:int,target的执行次数(尤其是当target在循环时)
            reg_str:str,寄存器名称
        return:
            int,int,表达式的最小值，最大值
        '''
        source_dctx = self.dctx[source_adr]
        # step1: 构建数据流图
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):# 判断分区间dfg是否已经构建
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count,self.ctx)
        # step2: 获得z3表达式
        if not (source_adr in self.z3expr.reg_expr and target_adr in self.z3expr.reg_expr[source_adr] and reg_str in self.z3expr.reg_expr[source_adr][target_adr]):
            min,max = self.z3expr.get_reg_range_by_vsa(self.dataflowgraph,source_adr,target_adr,reg_str,source_dctx)
        return min,max
    
    def check_data_dependency(self,source_adr,target1_adr,reg1_str,target2_adr,reg2_str):
        '''
        检查两条指令的寄存器是否存在数据流依赖
        args:
            source_adr:int,数据流分析的起点
            target1_adr:int,数据流分析的终点1
            reg1_str:str,数据流分析的终点1对应的寄存器名称
            target2_adr:int,数据流分析的终点2
            reg2_str:str,数据流分析的终点2对应的寄存器名称
        Returns :
            bool,target1和target2两条指令对应的寄存器是否存在数据流依赖
        '''
        source_dctx = self.dctx[source_adr]
        # step1: 构建数据流图
        if not (source_adr in self.dataflowgraph.gap_addrs and target1_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target1_adr,1)
        if not (source_adr in self.dataflowgraph.gap_addrs and target2_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target2_adr,1)
        # step2: 判断target1和target2相应的寄存器之间是否存在数据流依赖
        if not (source_adr in self.z3expr.reg_expr and target1_adr in self.z3expr.reg_expr[source_adr] and reg1_str in self.z3expr.reg_expr[source_adr][target1_adr]):
            if self.z3expr.check_data_dependency_by_vsa(self.dataflowgraph,source_adr,target1_adr,reg1_str,target2_adr,reg2_str,source_dctx):
                print("0x%x处的%s寄存器和0x%x处的%s寄存器之间存在数据流依赖"%(target1_adr,reg1_str,target2_adr,reg2_str))
                return True
            else:
                print("0x%x处的%s寄存器和0x%x处的%s寄存器之间不存在数据流依赖"%(target1_adr,reg1_str,target2_adr,reg2_str))
                return False

    def save_dctx(self,source_adr,target_adr,target_count,source_dctx,ctx):
        if not (source_adr in self.dataflowgraph.gap_addrs and target_adr in self.dataflowgraph.gap_addrs[source_adr]):
            self.dataflowgraph.constructDFGs(self.target_block,source_adr,target_adr,target_count)
        
        gap_source_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][0]
        gap_target_addrs = self.dataflowgraph.gap_addrs[source_adr][target_adr][1]
        for i in range(len(gap_source_addrs)):
            self.z3expr.vex_to_z3_in_dfg(self.dataflowgraph.dfgs[gap_source_addrs[i]][gap_target_addrs[i]],gap_source_addrs[i],gap_target_addrs[i])
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
