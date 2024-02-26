from pwn import *
from triton import *
from dataflow_analysis.data_flow_analyse import *
from config.config import *
from tqdm import tqdm
from copy import deepcopy
import sys
import string
import random
import json
if ANALYSE_MODE == 'X86':
    from utils.libc_func_mod32 import *
else:
    from utils.libc_func_mod64 import *

def interval_range_intersection(intervals, new_interval):
    intersections = []

    for interval in intervals:
        start = max(interval[0], new_interval[0])
        end = min(interval[1], new_interval[1])
        
        if start <= end:
            if start == new_interval[0]:
                return [[start, end]]
            intersections.append([start, end])

    return intersections

def loadBinary(ctx, path):
    import lief
    
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        
    
    for section in binary.sections:
        if section.name == ".plt":
            plt_base_address = section.virtual_address
            plt_size = section.size
            break
    return binary,plt_base_address,plt_size

def check_vsa_target(vsa_target_in,target_adr_count,pc):
    pc_count = target_adr_count[pc]
    for i in range(len(vsa_target_in)):
        target_adr = vsa_target_in[i]["target_adr"]
        if target_adr == pc:
            if target_adr_count[vsa_target_in[0]["target_adr"]] == 0: 
                target_adr_count[pc] -= 1 
                return None
            else:
                if pc_count == vsa_target_in[i]["target_count"]:
                    return i
                else:
                    return None

def print_message(vsa_target_out, Print_Payload):
    
    for i in range(len(vsa_target_out)):
        print("----------------------------------------------------------------------")
        print("target id:"+ str(vsa_target_out[i]["target_id"]) + "\t" + "target instruction:"+ vsa_target_out[i]["target_instruction"])
        if "dst_range" in vsa_target_out[i]:
            print("(dst)'s range:  [0x%x, 0x%x]"%(vsa_target_out[i]["dst_range"][0],vsa_target_out[i]["dst_range"][1]))
        if "src_range" in vsa_target_out[i]:
            print("(src)'s range:  [0x%x, 0x%x]"%(vsa_target_out[i]["src_range"][0],vsa_target_out[i]["src_range"][1]))
        if "len_range" in vsa_target_out[i]:
            print("(len)'s range:  [0x%x, 0x%x]"%(vsa_target_out[i]["len_range"][0],vsa_target_out[i]["len_range"][1]))
        if 'src_data_range' in vsa_target_out[i]:
            print("(src data)'s range:  [0x%x, 0x%x]"%(vsa_target_out[i]["src_data_range"][0],vsa_target_out[i]["src_data_range"][1]))
        if Print_Payload:
            print("one possible mix payload can be (%d bytes): "%(len(vsa_target_out[i]["mix_payload"])))
            print(vsa_target_out[i]["mix_payload"])
            with open('payload/mix/%s_0x%x_mix_payload.json'%(binary_name,vsa_target_out[i]["target_adr"]), 'w') as file:
                json.dump(vsa_target_out[i]["mix_payload"], file, indent=4)
            print("\n")
        print("----------------------------------------------------------------------\n\n")

def str_to_int(vsa_target_in):
    for i in range(len(vsa_target_in)):
        vsa_target_in[i]["source_adr"] = int(vsa_target_in[i]["source_adr"],16)
        vsa_target_in[i]["target_adr"] = int(vsa_target_in[i]["target_adr"],16)
        for j in range(len(vsa_target_in[i]["serial"])):
            vsa_target_in[i]["serial"][j] = int(vsa_target_in[i]["serial"][j], 16)
    return vsa_target_in

def sort_by_number(filename):
    
    number = int(''.join(filter(str.isdigit, filename)))
    return number
 
class Test():
    def __init__(self,ctx:TritonContext,entry_point=None,plt_base_address=None,plt_size=None) -> None:
        self.ctx=ctx
        self.ast = ctx.getAstContext()
        if entry_point is not None:
            self.initial_entry_point=entry_point 
        else:
            self.initial_entry_point=ctx.getConcreteRegisterValue(ctx.registers.rip) 
        self.plt_base_address = plt_base_address
        self.plt_size = plt_size

    def hookingHandler(self,ctx): 
        
        pc = ctx.getConcreteRegisterValue(ctx.registers.eip)
        hooking_flag = False
        for rel in customRelocation:
            if rel[2] == pc: 
                
                
                tmp= rel[1](ctx, None, None) 
                hooking_flag = True
                try:
                    ret_value=tmp[0]
                    ctx=tmp[1]
                except:
                    ret_value=tmp
                if ANALYSE_MODE == "X86":
                    ctx.setConcreteRegisterValue(ctx.registers.eax, ret_value)
                    
                    
                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.esp), CPUSIZE.DWORD))
                    
                    ctx.setConcreteRegisterValue(ctx.registers.eip, ret_addr)
                    
                    ctx.setConcreteRegisterValue(ctx.registers.esp, ctx.getConcreteRegisterValue(ctx.registers.esp)+CPUSIZE.DWORD) 
                else:
                    ctx.setConcreteRegisterValue(ctx.registers.rax, ret_value)
                    
                    
                    ret_addr = ctx.getConcreteMemoryValue(MemoryAccess(ctx.getConcreteRegisterValue(ctx.registers.rsp), CPUSIZE.QWORD))
                    
                    ctx.setConcreteRegisterValue(ctx.registers.rip, ret_addr)
                    
                    ctx.setConcreteRegisterValue(ctx.registers.rsp, ctx.getConcreteRegisterValue(ctx.registers.rsp)+CPUSIZE.QWORD) 
        return ctx,hooking_flag

    def run_dfa_by_poc(self,Print_Payload):
        

        self.label = Print_Payload
    
        pc = self.initial_entry_point

        Dataflow = DataflowAnalysis(self.ctx,pc,memoryCache,codeCache,self.plt_base_address,self.plt_size) 

        target_adr_count = {} 

        for i in range(len(vsa_target_in)) :
            target_adr = vsa_target_in[i]["target_adr"]
            target_adr_count[target_adr] = 0
        
        
        vsa_target_out = []
        result_num = 0

        
        while pc:
            
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16) 

            
            instruction = Instruction(pc, opcode)
            
            self.ctx.processing(instruction) 

            self.instruction = instruction

            self.ctx,hooking_flag = self.hookingHandler(self.ctx)
            
            Dataflow.collect_opcode(instruction,hooking_flag)

            if pc in target_adr_count:
                target_adr_count[pc]+=1
                pos = check_vsa_target(vsa_target_in,target_adr_count,pc)
                if pos != None:
                    tmp_target_out = {}
                    tmp_target_out["target_id"] = vsa_target_in[pos]["target_id"]
                    tmp_target_out["target_instruction"] = str(instruction)
                    tmp_target_out["target_adr"] = vsa_target_in[pos]["target_adr"]
                    dst_min,dst_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["dst_location"],vsa_target_in[pos]["target_count"],vsa_target_in[pos]["dst_reg"])
                    tmp_target_out["dst_range"] = [dst_min,dst_max]
                    src_min,src_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["src_location"],vsa_target_in[pos]["target_count"],vsa_target_in[pos]["src_reg"])
                    tmp_target_out["src_range"] = [src_min,src_max]
                    if 'len_reg' in vsa_target_in[pos]:
                        if vsa_target_in[pos]['len_location'] != None:
                            len_min,len_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["len_location"],vsa_target_in[pos]["target_count"],vsa_target_in[pos]["len_reg"])
                            tmp_target_out["len_range"] = [len_min,len_max]
                    if 'src_data_reg' in vsa_target_in[pos]:
                        if vsa_target_in[pos]['src_data_location'] != None:
                            src_data_min,src_data_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["src_data_location"],vsa_target_in[pos]["target_count"],vsa_target_in[pos]["src_data_reg"])
                            tmp_target_out["src_data_range"] = [src_data_min,src_data_max]
                    vsa_target_out.append(tmp_target_out)

                    if vsa_target_in[pos]["activated"]:
                        overlaps = Dataflow.get_memory_overlaps(codeCache + memoryCache, dst_min, dst_max, 'w')
                        start = overlaps[0]['start']
                        size = overlaps[0]['size']
                        for indx in range(size):
                            ctx.taintMemory(MemoryAccess(start+indx,CPUSIZE.BYTE)) 
                            ctx.symbolizeMemory(MemoryAccess(start+indx,CPUSIZE.BYTE))
                        Dataflow.save_dctx(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["target_adr"],vsa_target_in[pos]["target_count"],Dataflow.dctx[vsa_target_in[pos]["source_adr"]],ctx)
                    
                    if Print_Payload:
                        regs_as_value = []
                        regs_as_addr = []
                        target_values = []
                        target_mems = [] 
                        if vsa_target_in[pos]["dst_value"] != None:
                            regs_as_value.append(vsa_target_in[pos]["dst_reg"])
                            target_values.append(vsa_target_in[pos]["dst_value"])
                        if vsa_target_in[pos]["src_value"] != None:
                            regs_as_value.append(vsa_target_in[pos]["src_reg"])
                            target_values.append(vsa_target_in[pos]["src_value"])
                        if vsa_target_in[pos]["src_mem_value"] != None:
                            regs_as_addr.append(vsa_target_in[pos]["src_reg"])
                            target_mems.append(vsa_target_in[pos]["src_mem_value"])

                        mix_payload = Dataflow.get_origin_mem_by_mix_expr(regs_as_value, target_values, regs_as_addr, target_mems, vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["target_adr"],vsa_target_in[pos]["target_count"])
                        vsa_target_out[pos]["mix_payload"] = mix_payload
                    
                    if Check_Stitch and pos == (len(vsa_target_in) - 1):
                        check_flag = Dataflow.check_data_dependency(vsa_target_in[pos]["source_adr"], vsa_target_in[pos-1]["dst_location"],vsa_target_in[pos-1]["dst_reg"], vsa_target_in[pos]["src_location"], vsa_target_in[pos]["src_reg"])
                        if check_flag:
                            print("stitch success")
                        else:
                            print("stitch fail")

                    result_num += 1

            if ANALYSE_MODE == "X64":
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.rip)
            else:
                pc = self.ctx.getConcreteRegisterValue(self.ctx.registers.eip)
                
            if len(vsa_target_in) == result_num:
                break

        return vsa_target_out
    
    def run_dfa_by_one_path(self, Print_Payload, p_file_path, useful_mem):
        
        with open(p_file_path,'r') as f:
            vsa_target_in = json.load(f)

        pc = vsa_target_in[0]["serial"][0]

        Dataflow = DataflowAnalysis(self.ctx,pc,memoryCache,codeCache,self.plt_base_address,self.plt_size) 
        target_adr_count = {} 

        for i in range(len(vsa_target_in)) :
            target_adr = vsa_target_in[i]["target_adr"]
            target_adr_count[target_adr] = 0
        
        vsa_target_out = []
        result_num = 0

        pc_list = deepcopy(vsa_target_in[0]["serial"])
        if Activated:
            pc_list.extend(vsa_target_in[1]["serial"])
        if Check_Stitch:
            pc_list = vsa_target_in[1]["serial"]
        if Activated:
            vsa_target_in[1]["source_adr"] = vsa_target_in[0]["serial"][-1]
        
        for pc in pc_list:
            
            opcode = self.ctx.getConcreteMemoryAreaValue(pc, 16) 

            
            instruction = Instruction(pc, opcode)
            
            self.ctx.processing(instruction)      
    
            self.instruction = instruction

            self.ctx,hooking_flag = self.hookingHandler(self.ctx)

            
            Dataflow.collect_opcode(instruction,hooking_flag)

            if pc in target_adr_count:
                target_adr_count[pc] += 1
                pos = check_vsa_target(vsa_target_in,target_adr_count,pc) 
                if pos != None:
                    tmp_target_out = {}
                    tmp_target_out["target_id"] = vsa_target_in[pos]["target_id"]
                    tmp_target_out["target_instruction"] = str(instruction)
                    start_time = time.time()
                    if 'dst_reg' in vsa_target_in[pos]:
                        if vsa_target_in[pos]['dst_reg']['base'] != None:
                            dst_min,dst_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["dst_location"],vsa_target_in[pos]["dst_count"],vsa_target_in[pos]["dst_reg"])
                            tmp_target_out["dst_range"] = [dst_min,dst_max]
                    if 'src_reg' in vsa_target_in[pos]:
                        if vsa_target_in[pos]['src_reg']['base'] != None:
                            src_min,src_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["src_location"],vsa_target_in[pos]["src_count"],vsa_target_in[pos]["src_reg"])
                            tmp_target_out["src_range"] = [src_min,src_max]
                    if 'src_data_reg' in vsa_target_in[pos]:
                        if isinstance(vsa_target_in[pos]['src_data_reg'], dict) and vsa_target_in[pos]['src_data_reg']['base'] != None:
                            src_data_min,src_data_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["src_data_location"],vsa_target_in[pos]["src_data_count"],vsa_target_in[pos]["src_data_reg"])
                            tmp_target_out["src_data_range"] = [src_data_min,src_data_max]
                        if isinstance(vsa_target_in[pos]['src_data_reg'], str) and vsa_target_in[pos]['src_data_reg'] != None:
                            src_data_min,src_data_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["src_data_location"],vsa_target_in[pos]["src_data_count"],vsa_target_in[pos]["src_data_reg"])
                            tmp_target_out["src_data_range"] = [src_data_min,src_data_max]

                    if "len_reg" in vsa_target_in[pos]:
                        if vsa_target_in[pos]['len_reg']['base'] != None:
                            len_min,len_max = Dataflow.get_expr_range_in_dfgs(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["len_location"],vsa_target_in[pos]["len_count"],vsa_target_in[pos]["len_reg"])
                            tmp_target_out["len_range"] = [len_min,len_max]
                    end_time = time.time()
                    run_time = end_time - start_time
                    tmp_target_out["run_time"] = run_time
                    vsa_target_out.append(tmp_target_out)

                    
                    if Activated and pos == 0:
                        
                        overlaps = interval_range_intersection(useful_mem, (dst_min,dst_max))
                        for overlap in overlaps:
                            for addr in range(overlap[0],overlap[1]):
                                ctx.taintMemory(MemoryAccess(addr, CPUSIZE.BYTE)) 
                                ctx.symbolizeMemory(MemoryAccess(addr, CPUSIZE.BYTE))
                        Dataflow.save_dctx(vsa_target_in[pos]["source_adr"],vsa_target_in[pos]["target_adr"],vsa_target_in[pos]["target_count"],Dataflow.dctx[vsa_target_in[pos]["source_adr"]],ctx)
                    
                    if Print_Payload:
                        regs_as_value = []
                        regs_as_addr = []
                        target_values = []
                        target_mems = [] 
                        if vsa_target_out[pos]["dst_value"] != None:
                            regs_as_value.append(vsa_target_out[pos]["dst_reg"])
                            target_values.append(vsa_target_out[pos]["dst_value"])
                        if vsa_target_out[pos]["src_value"] != None:
                            regs_as_value.append(vsa_target_out[pos]["src_reg"])
                            target_values.append(vsa_target_out[pos]["src_value"])
                        if vsa_target_out[pos]["src_mem_value"] != None:
                            regs_as_addr.append(vsa_target_out[pos]["src_reg"])
                            target_mems.append(vsa_target_out[pos]["src_mem_value"])
                        mix_payload = Dataflow.get_origin_mem_by_mix_expr(regs_as_value, target_values, regs_as_addr, target_mems, vsa_target[pos]["source_adr"],vsa_target[pos]["target_adr"],vsa_target[pos]["target_count"])
                        vsa_target_out[pos]["mix_payload"] = mix_payload
                    
                    if Check_Stitch and pos == (len(vsa_target_in) - 1):
                        check_flag = Dataflow.check_data_dependency(vsa_target_in[pos]["source_adr"], vsa_target_in[pos-1]["dst_location"],vsa_target_in[pos-1]["dst_reg"], vsa_target_in[pos]["src_location"], vsa_target_in[pos]["src_reg"])
                        if check_flag:
                            print("True")
                        else:
                            print("False")
                        exit(0)
                    result_num += 1
                
            if len(vsa_target_in) == result_num:
                break

        return vsa_target_out
    
    def run_dfa_by_all_path(self,Print_Payload,p_dir_path):
        
        file_list = os.listdir(p_dir_path)
        file_list = sorted(file_list, key=sort_by_number)
        
        progress_bar = tqdm(total=len(file_list), desc="Processing files", unit="file")
        start_time = time.time()
         
        for filename in file_list:
            filepath = os.path.join(p_dir_path, filename)
            if os.path.isfile(filepath):
                
                
                vsa_target_out = self.run_dfa_by_one_path(Print_Payload, filepath)
                print("current path file:%s\n"%filename)
                
                print_message(vsa_target_out, Print_Payload)
                
                outdir = "out/%s/P1_VSA"%binary_name
                os.makedirs(outdir, exist_ok=True)
                outfile = os.path.join(outdir, filename)
                with open(outfile, "w") as f:
                    json.dump(vsa_target_out, f, indent=4)
            
            progress_bar.update(1)
            current_time = time.time()
            elapsed_time = current_time - start_time
            
            print("Time elapsed for iteration {}: {:.2f} seconds".format(progress_bar.n, elapsed_time))
            del self.ctx
            self.ctx = fresh()
        
        progress_bar.close()


def makeRelocation(ctx, binary, base_adr):
    
    for pltIndex in range(len(customRelocation)):
        customRelocation[pltIndex][2] = BASE_PLT + pltIndex

    
    pltgots=[]
    
    relocations = [x for x in binary.pltgot_relocations]
    
    if ANALYSE_MODE == "X64":
        got_table_adr=relocations[0].address - 0x18 
    else:
        got_table_adr=relocations[0].address - 0xc 
    for rel in relocations:
        symbolName = rel.symbol.name
        if '.so' in binary_path:
            symbolRelo = rel.address - got_table_adr + base_adr
        else:
            symbolRelo = rel.address
        flag = 0
        for crel in customRelocation:
            if symbolName == crel[0]:
                if ANALYSE_MODE == "X86":
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.DWORD), crel[2])
                else:
                    ctx.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
                
                flag=1
                break
        if flag==0:
            adr = (ctx.getConcreteMemoryAreaValue(symbolRelo, 8))
            adr = adr[::-1]
            pltgots.append([symbolName,hex(symbolRelo),int(adr.hex(),16)])
    return


memoryCache = list()

codeCache = list()


def Caching(ctx, mem):
    addr = mem.getAddress()
    size = mem.getSize()
    
    for index in range(size):
        if not ctx.isConcreteMemoryValueDefined(addr+index, 1):
            for r in memoryCache + codeCache:
                if addr+index >= r['start'] and addr+index < r['start'] + r['size']:
                    i = ((addr + index) - r['start'])
                    value = ord(r['memory'][i : i+1])
                    ctx.setConcreteMemoryValue(addr+index, value)
                    

    return

def load_dump(ctx, path, binary_name):
    global memoryCache
    global codeCache

    with open(path,'rb') as file:
        data = pickle.load(file,encoding='iso-8859-1')

    
    regs = data[0]
    mems = data[1]
    codes = data[2]
    args = data[3]
    
    
    for reg_name in regs:
        try:
            Reg = ctx.getRegister(reg_name)
            ctx.setConcreteRegisterValue(Reg, regs[reg_name])
        except Exception as e:
            
            print(f"Error setting register {reg_name}: {str(e)}")
    
    if 'rip' in regs:
        entrypoint = regs['rip']
    else:
        entrypoint = regs['eip']
    
    
    useful_mem = []
    for mem in mems:
        start = mem['start']
        end   = mem['end']
        name = mem['name']
        permissions = mem['permissions']
        if mem['memory']:
            memoryCache.append({
                'start':  start,
                'size':   end - start,
                'memory': mem['memory'],
                'permissions': permissions,
            })
        argv1=str(binary_path).split('/')[-1] 
        
        if argv1 in name and 'rw' in permissions:
            base_got_adr=start

        if (binary_name in mem['name'] or '[heap]' in mem['name'] or '[stack]' in mem['name']  or 'mapped' in mem['name']) and 'rw-p' in permissions:
            useful_mem.append([start, end])
    
    for code in codes:
        start = code['start']
        end   = code['end']
        permissions = code['permissions']
        if code['memory']:
            codeCache.append({
                'start':  start,
                'size':   end - start,
                'memory': code['memory'],
                'permissions': permissions,
            })
        if binary_name in code['name']:
            code_base_adr = code['start']

    return entrypoint,base_got_adr,args,code_base_adr,useful_mem

def fresh():
    if ANALYSE_MODE == "X86": 
        
        ctx = TritonContext(ARCH.X86)
        
        ctx.setArchitecture(ARCH.X86)
    else:
        ctx = TritonContext(ARCH.X86_64)
        
        ctx.setArchitecture(ARCH.X86_64)

    
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    
    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)

    
    ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, Caching)
    
    binary,plt_base_address,plt_size = loadBinary(ctx, binary_path)

    entrypoint,base_got_adr,args,code_base_adr,useful_mem = load_dump(ctx,dump_path,binary_path.split('/')[-1])
    
    makeRelocation(ctx, binary, base_got_adr)

    
    for mem in tainted_mem:
        for indx in range(tainted_mem[mem]):
            ctx.taintMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE)) 
            ctx.symbolizeMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE))
    return ctx

def initialize():
    if ANALYSE_MODE == "X86": 
        
        ctx = TritonContext(ARCH.X86)
        
        ctx.setArchitecture(ARCH.X86)
    else:
        ctx = TritonContext(ARCH.X86_64)
        
        ctx.setArchitecture(ARCH.X86_64)

    
    ctx.setMode(MODE.ALIGNED_MEMORY, True)

    ctx.setAstRepresentationMode(AST_REPRESENTATION.PYTHON)
    
    ctx.addCallback(CALLBACK.GET_CONCRETE_MEMORY_VALUE, Caching)
    
    binary,plt_base_address,plt_size = loadBinary(ctx, binary_path)

    entrypoint,base_got_adr,args,code_base_adr,useful_mem = load_dump(ctx,dump_path,binary_path.split('/')[-1])
    
    makeRelocation(ctx, binary, base_got_adr)

    for mem in tainted_mem:
        for indx in range(tainted_mem[mem]):
            ctx.taintMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE)) 
            ctx.symbolizeMemory(MemoryAccess(mem+indx,CPUSIZE.BYTE))
    return ctx,entrypoint,args,code_base_adr,plt_base_address,plt_size,useful_mem


if __name__=='__main__':     
    
    ctx,entry_point,args,code_base_adr,plt_base_address,plt_size,useful_mem=initialize()

    my_analyser=Test(ctx, entry_point,plt_base_address,plt_size) 
    
    if len(sys.argv) > 1:
        
        vsa_target_out = my_analyser.run_dfa_by_one_path(Print_Payload, sys.argv[1], useful_mem)
        print("current path file:%s\n"%((sys.argv[1]).split('/')[-1]))
        
        print_message(vsa_target_out, Print_Payload)
        
        outdir = "out/%s/P1_VSA"%binary_name
        if Activated:
            outdir = "out/%s/P1P2_VSA"%binary_name
        os.makedirs(outdir, exist_ok=True)
        filename = (sys.argv[1]).split('/')[-1]
        outfile = os.path.join(outdir, filename)
        with open(outfile, "w") as f:
            json.dump(vsa_target_out, f, indent=4)
    else:
        vsa_target_out = my_analyser.run_dfa_by_poc(Print_Payload)
        print_message(vsa_target_out,Print_Payload)
        out_directory = "out/%s"%binary_name
        os.makedirs(out_directory, exist_ok=True)
        filename = "%s.json"%(dump_path.split('/')[-1])
        filepath = os.path.join(out_directory, filename)
        with open(filepath, "w") as f:
            json.dump(vsa_target_out, f, indent=4)
