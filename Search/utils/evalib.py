'''
    该文件用于收集实验数据
'''
from triton import TritonContext, ARCH, MemoryAccess, CPUSIZE, Instruction, OPCODE, MODE, OPERAND,AST_REPRESENTATION,CALLBACK
from utils.tool_lib import is_op_equal,twos_complement_to_int,extract_parts
from config.__config import *
import json
import sys
import os
import hashlib
import time
import re
SAVED_DIR = None
# 用于存储程序中执行的指令
class inst_saver():
    def __init__(self,G1=None,save_path=None):
        if save_path is None:
            global SAVED_DIR
            SAVED_DIR = sys.argv[1].split('/')[-1] + "_P1"
            if not os.path.exists(SAVED_DIR):
                os.makedirs(SAVED_DIR)
                print("Make Dir:", SAVED_DIR)
            else:
                print("Exists:", SAVED_DIR)
        else:
            self.save_dir = save_path
            if not os.path.exists(save_path):
                os.makedirs(save_path)
                print("Make Dir：", save_path)
            else:
                print("Exists:", save_path)
        self.path_list = []
        if G1 is not None:
            self.G1 = G1
        else:
            self.G1 = {"target_id": 0, # 标记gadget的id
                                "target_type": None, # 标记gadget的属性
                                "source_adr": None, # 值集分析的起点
                                "target_adr": None, # gadget的位置
                                "target_count":1, # gadget的执行次数
                                "dst_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},# 写寄存器信息
                                "dst_location": None, # 写寄存器的指令地址
                                "src_reg": {'base':None,'idx':None,'imm1':1,'imm2':0}, # 读寄存器信息
                                "src_location": None, # 读寄存器的指令地址
                                "len_reg":{'base':None,'idx':None,'imm1':1,'imm2':0}, # 内存操作长度寄存器
                                "len_location": None, # 长度寄存器的指令地址
                                "dst_value": None, # dst寄存器期望的值
                                "src_value": None, # src寄存器期望的值
                                "src_mem_value": None, # src寄存器对应内存期望的值 
                                "len_value":None, # len寄存器期望的值
                                "src_mem" : {'base':None,'idx':None,'imm1':1,'imm2':0},
                                # 用于存储固定地址读时，读出的数据的取值范围
                                "src_data_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},
                                "src_data_location": None,
                                "serial": []}
        


        self.G2 = {"target_id": 0, # 标记gadget的id
                            "target_type": None, # 标记gadget的属性
                            "source_adr": None, # 值集分析的起点
                            "target_adr": None, # gadget的位置
                            "target_count":1, # gadget的执行次数
                            "dst_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},# 写寄存器信息
                            "dst_location": None, # 写寄存器的指令地址
                            "src_reg": {'base':None,'idx':None,'imm1':1,'imm2':0}, # 读寄存器信息
                            "src_location": None, # 读寄存器的指令地址
                            "len_reg":{'base':None,'idx':None,'imm1':1,'imm2':0}, # 内存操作长度寄存器
                            "len_location": None, # 长度寄存器的指令地址
                            "dst_value": None, # dst寄存器期望的值
                            "src_value": None, # src寄存器期望的值
                            "src_mem_value": None, # src寄存器对应内存期望的值 
                            "len_value":None, # len寄存器期望的值
                            "src_mem" : {'base':None,'idx':None,'imm1':1,'imm2':0},
                            # 用于存储固定地址读时，读出的数据的取值范围
                            "src_data_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "src_data_location": None,

                            "serial": []}
        self.serial_list = []
        self.seq_num = 0
    
    # 添加指令序列
    def solve(self, pc:str):
        self.serial_list.append(int(pc, 16))
    def save_path(self,inst):
        self.path_list.append(inst.getAddress())
    # 清理当前的指令缓存
    def clearG1(self):
        self.G1 = {"target_id": 0, # 标记gadget的id
                            "target_type": None, # 标记gadget的属性
                            "source_adr": None, # 值集分析的起点
                            "target_adr": None, # gadget的位置
                            "target_count":1, # gadget的执行次数
                            "dst_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},# 写寄存器信息
                            "dst_location": None, # 写寄存器的指令地址
                            "src_reg": {'base':None,'idx':None,'imm1':1,'imm2':0}, # 读寄存器信息
                            "src_location": None, # 读寄存器的指令地址
                            "len_reg":{'base':None,'idx':None,'imm1':1,'imm2':0}, # 内存操作长度寄存器
                            "len_location": None, # 长度寄存器的指令地址
                            "dst_value": None, # dst寄存器期望的值
                            "src_value": None, # src寄存器期望的值
                            "src_mem_value": None, # src寄存器对应内存期望的值 
                            "src_mem" : {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "len_value":None, # len寄存器期望的值
                            # 用于存储固定地址读时，读出的数据的取值范围
                            "src_data_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "src_data_location": None,
                            "serial": []}
        
        self.G2 = {"target_id": 0, # 标记gadget的id
                            "target_type": None, # 标记gadget的属性
                            "source_adr": None, # 值集分析的起点
                            "target_adr": None, # gadget的位置
                            "target_count":1, # gadget的执行次数
                            "dst_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},# 写寄存器信息
                            "dst_location": None, # 写寄存器的指令地址
                            "src_reg": {'base':None,'idx':None,'imm1':1,'imm2':0}, # 读寄存器信息
                            "src_location": None, # 读寄存器的指令地址
                            "len_reg":{'base':None,'idx':None,'imm1':1,'imm2':0}, # 内存操作长度寄存器
                            "len_location": None, # 长度寄存器的指令地址
                            "dst_value": None, # dst寄存器期望的值
                            "src_value": None, # src寄存器期望的值
                            "src_mem_value": None, # src寄存器对应内存期望的值 
                            "len_value":None, # len寄存器期望的值
                            # 用于存储固定地址读时，读出的数据的取值范围
                            "src_mem" : {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "src_data_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "src_data_location": None,
                            "serial": []}
    def clearG2(self):
        self.G2 = {"target_id": 0, # 标记gadget的id
                            "target_type": None, # 标记gadget的属性
                            "source_adr": None, # 值集分析的起点
                            "target_adr": None, # gadget的位置
                            "target_count":1, # gadget的执行次数
                            "dst_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},# 写寄存器信息
                            "dst_location": None, # 写寄存器的指令地址
                            "src_reg": {'base':None,'idx':None,'imm1':1,'imm2':0}, # 读寄存器信息
                            "src_location": None, # 读寄存器的指令地址
                            "len_reg":{'base':None,'idx':None,'imm1':1,'imm2':0}, # 内存操作长度寄存器
                            "len_location": None, # 长度寄存器的指令地址
                            "dst_value": None, # dst寄存器期望的值
                            "src_value": None, # src寄存器期望的值
                            "src_mem_value": None, # src寄存器对应内存期望的值 
                            "len_value":None, # len寄存器期望的值
                            "src_mem" : {'base':None,'idx':None,'imm1':1,'imm2':0},
                            # 用于存储固定地址读时，读出的数据的取值范围
                            "src_data_reg": {'base':None,'idx':None,'imm1':1,'imm2':0},
                            "src_data_location": None,
                            "serial": []}
    #  存储数据
    def finish_saveG2(self, ctx, new_gadget, file_name:str, angr_proj,code_base,save_dir =None):
        global SAVED_DIR
        SAVED_DIR = sys.argv[1].split('/')[-1] + "_P1P2"
        if len(self.serial_list) == 0:
            print("INSTRUCTIONS NOT ENOUGH")
            return 
        self.G2["serial"] = self.serial_list
        # 这里用于暂存本次写入的数据的临时操作数
        write_data_op = None
        # is_op_equal
        # 这里从后向前遍历
        g_type = None
        dest_taint = False
        src_taint = False
        value_taint = False
        loop_taint = False
        if len(new_gadget.instructions) == 1:
            self.clearG2()
            return
        if '_libc32' in  new_gadget.gadget_type: # 这里有可能是strcpy这种只有两个参数的原语
            # 第一个
            print(str(new_gadget.instructions[1].instruction.getOperands()[-1]))
            new_gadget.instructions[0].instruction # dest
            new_gadget.instructions[1].instruction # src
            if len(new_gadget.instructions) == 4 : # 这里证明是三操作数，则有len可取
                new_gadget.instructions[2].instruction # len
                self.G2['len_reg']['base'] = str(new_gadget.instructions[2].instruction.getOperands()[-1]).split(':')[0]
                self.G2['len_location'] = new_gadget.instructions[2].instruction.getAddress()    
            
            self.G2['dst_reg']['base'] = str(new_gadget.instructions[0].instruction.getOperands()[-1]).split(':')[0]
            self.G2['dst_location'] = new_gadget.instructions[0].instruction.getAddress()
            if new_gadget.instructions[0].instruction.isTainted:
                dest_taint = True
            self.G2['src_reg']['base'] = str(new_gadget.instructions[1].instruction.getOperands()[-1]).split(':')[0]
            self.G2['src_location'] = new_gadget.instructions[1].instruction.getAddress()

            # 检查是否是push [mem]
            if len(re.findall(r'\[(.*)\]', str(new_gadget.instructions[1].instruction))) != 0:
                base_reg,idx_reg,imm1,imm2 = extract_parts(re.findall(r'\[(.*)\]', str(new_gadget.instructions[1].instruction))[0])
                self.G2['src_mem']['base'] = base_reg
                self.G2['src_mem']['idx'] = idx_reg
                if imm1 is not None:
                    self.G2['src_mem']['imm1'] = int(imm1)
                if imm2 is not None:
                    self.G2['src_mem']['imm2'] = int(imm2)
            else:
                # 这里是push寄存器，push eax,则取出eax
                self.G2['src_mem']['base'] = str(new_gadget.instructions[1].instruction).split()[-1]
            if new_gadget.instructions[1].instruction.isTainted:
                src_taint = True
            
        elif '_libc' in new_gadget.gadget_type:
            '''
                这里遍历每一个指令分别去寻找对应的寄存器即可
            '''
            get_rdi = False
            get_rsi = False
            get_rdx = False
            # 这类直接继承相应的libc
            self.G2['target_type'] =  new_gadget.gadget_type
            new_gadget.instructions.reverse()
            for inst_obj in new_gadget.instructions:
                # 这里第一个操作数一定是写入操作数，在这里依次找rdi rsi rdx
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rdx') and not get_rdx:
                    self.G2['len_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    get_rdx = True
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rdi') and not get_rdi:
                    self.G2['dst_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    get_rdi = True
                    if ctx.isRegisterTainted(inst_obj.instruction.getOperands()[0]):
                        dest_taint = True
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rsi') and not get_rsi:
                    self.G2['src_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    # 这里记录源数据所在的内存
                    self.G2['src_mem']['base'] = self.G2['src_reg']['base']
                    get_rsi = True
                    if ctx.isRegisterTainted(inst_obj.instruction.getOperands()[0]):
                        src_taint = True
            '''
                这里全部定为最后一条指令的位置
            '''
            self.G2['dst_location'] = self.serial_list[-1]
            self.G2['src_location'] = self.serial_list[-1]
            self.G2['len_location'] = self.serial_list[-1]
            new_gadget.instructions.reverse()
        else:
            '''
                这里处理指令序列gadget
            '''
            new_gadget.instructions.reverse()
            for inst_obj in new_gadget.instructions:
                '''
                    处理写回指令
                '''
                if inst_obj.instruction.isMemoryWrite():
                    # gadget中的写回永远是最后一个 [.] 0x7fffe6281a9c: mov byte ptr [rax + rdx], sil
                    self.G2["src_location"] = inst_obj.instruction.getAddress()
                    tmp_op = inst_obj.instruction.getOperands()
                    if tmp_op[0].getType() == OPERAND.MEM:

                        if ctx.isMemoryTainted(tmp_op[0]):
                            value_taint = True
                        if 'unknown' not in str(tmp_op[0].getBaseRegister()):
                            self.G2['dst_reg']['base'] =  str(tmp_op[0].getBaseRegister()).split(':')[0]
                            if ctx.isRegisterTainted(tmp_op[0].getBaseRegister()):
                                dest_taint = True
                        if 'unknown' not in str(tmp_op[0].getIndexRegister()):
                            self.G2['dst_reg']['idx'] =  str(tmp_op[0].getIndexRegister()).split(':')[0]
                            if ctx.isRegisterTainted(tmp_op[0].getIndexRegister()):
                                dest_taint = True
                        # 这里的倍数能看到
                        self.G2['dst_reg']['imm1'] =  int(str(tmp_op[0].getScale()).split(':')[0], 16)
                        # 但是相加的立即数看不到 # TODO 这里遇到相应的指令之后再看
                        self.G2['dst_reg']['imm2'] =  twos_complement_to_int(str(tmp_op[0].getDisplacement()).split(':')[0])
                        self.G2["dst_location"] = inst_obj.instruction.getAddress()
                    else:
                        raise Exception("Not A Memory Write inst!!!")
                    
                    if tmp_op[-1].getType() == OPERAND.REG:
                        # 这里向上找从哪里load出来的
                        write_data_op = tmp_op

                elif inst_obj.instruction.isMemoryRead():
                    '''
                        这里处理读出指令
                    '''
                    tmp_op = inst_obj.instruction.getOperands()
                    # 这里检查左操作数是否是最终写入目标地址的数据，如果是则直接取出其读指针
                    if tmp_op[0].getType() == OPERAND.REG:
                        if is_op_equal(str(write_data_op[-1]).split(':')[0],str(tmp_op[0]).split(':')[0]):
                            # 这里找到是何时读入的,如果是这里的就将这里视为最终地址
                            if 'unknown' not in str(tmp_op[-1].getBaseRegister()):
                                self.G2['src_reg']['base'] =  str(tmp_op[-1].getBaseRegister()).split(':')[0]
                                if ctx.isRegisterTainted(tmp_op[-1].getBaseRegister()):
                                    src_taint = True
                            if 'unknown' not in str(tmp_op[-1].getIndexRegister()):
                                self.G2['src_reg']['idx'] =  str(tmp_op[-1].getIndexRegister()).split(':')[0]
                                if ctx.isRegisterTainted(tmp_op[-1].getIndexRegister()):
                                    src_taint = True
                            # if src_taint is False:
                            #     # 这里证明源地址不受污染，那就求解源数据的取值范围
                            self.G2["src_data_reg"]["base"] = str(write_data_op[-1]).split(':')[0]
                            self.G2["src_data_location"] = inst_obj.instruction.getAddress()
                            # 这里的倍数能看到
                            self.G2['src_reg']['imm1'] =  int(str(tmp_op[-1].getScale()).split(':')[0], 16)
                            # 但是相加的立即数看不到 # TODO 这里遇到相应的指令之后再看
                            self.G2['src_reg']['imm2'] =  twos_complement_to_int(str(tmp_op[-1].getDisplacement()).split(':')[0])


                            if  is_op_equal(str(tmp_op[0]).split(':')[0] , str(tmp_op[-1].getBaseRegister()).split(':')[0]) or\
                                is_op_equal(str(tmp_op[0]).split(':')[0] , str(tmp_op[-1].getIndexRegister()).split(':')[0]):
                                for i in range(len(self.serial_list)):
                                    if self.serial_list[i] == inst_obj.instruction.getAddress():
                                        self.G2["src_location"] = self.serial_list[i-1]
                            else:
                                self.G2["src_location"] = inst_obj.instruction.getAddress()
                else:
                    '''
                        mov 或者运算指令，如果是mov指令则可能要将write_data_op进行替换
                    '''
                    import os
                    os.system("echo "+str(inst_obj.instruction) + "> WRONG_INST.txt")
            
            new_gadget.instructions.reverse()
        
        if dest_taint is True:
            if src_taint is True:
                self.G2["target_type"] = "AMC" # 1 1 x
            elif value_taint is True:
                self.G2["target_type"] = "AMW" # 1 0 1
            else:
                self.G2["target_type"] = "SVW" # 1 0 0 源地址和源内容都无法改变 State Value Write
        elif src_taint is True:
            self.G2["target_type"] = "AMR" # 0 1 x
        else:
            self.G2["target_type"] = "USELESS" # 0 0 x
            # 这里直接return，不进行任何的操作
            self.clearG2()
            print("[DEBUG] Useless Gadget")
            return

        self.seq_num += 1
        self.G2["target_id"] = self.seq_num
        self.G2["source_adr"] = self.G2["serial"][0]
        self.G2["target_adr"] = self.G2["serial"][-1]

        if self.G2["dst_reg"]["base"] is None or  self.G2["src_reg"]["base"] is None:
            print("EROOR FOUND REG")
            self.clearG2()
            return
        if 'sp' in self.G2["dst_reg"]["base"] or 'sp' in self.G2["src_reg"]["base"]:
            print("VARIABLE SEND")
            self.clearG2()
            return
            # raise Exception("EROOR FOUND REG")
        # 将对象保存到JSON文件
        if self.save_dir is None:
            with open(SAVED_DIR+"/"+file_name+'_'+hashlib.sha256(str(time.time()).encode()).hexdigest()+".json", 'w') as f:
                # print(self.G2)
                # print(loop_taint)
                json.dump([self.G1,self.G2], f, indent=4)
        else:
            with open(self.save_dir+"/"+file_name+'_'+hashlib.sha256(str(time.time()).encode()).hexdigest()+".json", 'w') as f:
                # print(self.G2)
                # print(loop_taint)
                json.dump([self.G1,self.G2], f, indent=4)

        # 清理当前Gadget的信息
        self.clearG2()

    #  存储数据
    def finish_saveG1(self, ctx, new_gadget, file_name:str, angr_proj,code_base):
        self.clearG1()
        self.G1["serial"] = self.serial_list
        # 这里用于暂存本次写入的数据的临时操作数
        write_data_op = None
        # is_op_equal
        # 这里从后向前遍历
        g_type = None
        dest_taint = False
        src_taint = False
        value_taint = False
        loop_taint = False
        if len(new_gadget.instructions) == 1:
            return
        if '_libc32' in  new_gadget.gadget_type: # 这里有可能是strcpy这种只有两个参数的原语
            # 第一个
            print(str(new_gadget.instructions[1].instruction.getOperands()[-1]))
            new_gadget.instructions[0].instruction # dest
            new_gadget.instructions[1].instruction # src
            if len(new_gadget.instructions) == 4 : # 这里证明是三操作数，则有len可取
                new_gadget.instructions[2].instruction # len
                self.G1['len_reg']['base'] = str(new_gadget.instructions[2].instruction.getOperands()[-1]).split(':')[0]
                self.G1['len_location'] = new_gadget.instructions[2].instruction.getAddress()    
            self.G1['dst_reg']['base'] = str(new_gadget.instructions[0].instruction.getOperands()[-1]).split(':')[0]
            self.G1['dst_location'] = new_gadget.instructions[0].instruction.getAddress()
            if new_gadget.instructions[0].instruction.isTainted:
                dest_taint = True
            self.G1['src_reg']['base'] = str(new_gadget.instructions[1].instruction.getOperands()[-1]).split(':')[0]
            self.G1['src_location'] = new_gadget.instructions[1].instruction.getAddress()
            if new_gadget.instructions[1].instruction.isTainted:
                src_taint = True
            
        elif '_libc' in new_gadget.gadget_type:
            '''
                这里遍历每一个指令分别去寻找对应的寄存器即可
            '''
            get_rdi = False
            get_rsi = False
            get_rdx = False
            # 这类直接继承相应的libc
            self.G1['target_type'] =  new_gadget.gadget_type
            new_gadget.instructions.reverse()
            for inst_obj in new_gadget.instructions:
                # 这里第一个操作数一定是写入操作数，在这里依次找rdi rsi rdx
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rdx') and not get_rdx:
                    self.G1['len_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    get_rdx = True
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rdi') and not get_rdi:
                    self.G1['dst_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    if ctx.isRegisterTainted(inst_obj.instruction.getOperands()[0]):
                        dest_taint = True
                    get_rdi = True
                if is_op_equal(str(inst_obj.instruction.getOperands()[0]).split(':')[0], 'rsi') and not get_rsi:
                    self.G1['src_reg']['base'] = str(inst_obj.instruction.getOperands()[0]).split(':')[0]
                    get_rsi = True
                    if ctx.isRegisterTainted(inst_obj.instruction.getOperands()[0]):
                        src_taint = True
            '''
                这里全部定为最后一条指令的位置
            '''
            self.G1['dst_location'] = self.serial_list[-1]
            self.G1['src_location'] = self.serial_list[-1]
            self.G1['len_location'] = self.serial_list[-1]
            new_gadget.instructions.reverse()
        else:
            '''
                这里处理指令序列gadget
            '''
            new_gadget.instructions.reverse()
            for inst_obj in new_gadget.instructions:
                # print("+++++++++++++++++++++++++++++++++++")
                # print(inst_obj.instruction)
                # print("getOperands()",inst_obj.instruction.getOperands())
                # print("getReadRegisters()",inst_obj.instruction.getReadRegisters()) # 
                # print("getWrittenRegisters()",inst_obj.instruction.getWrittenRegisters())
                # print("getStoreAccess()",inst_obj.instruction.getStoreAccess())
                # print("getReadImmediates()",inst_obj.instruction.getReadImmediates())
                # print("getLoadAccess()",inst_obj.instruction.getLoadAccess())
                # print("isMemoryWrite:",inst_obj.instruction.isMemoryWrite())
                # print("isMemoryRead:",inst_obj.instruction.isMemoryRead())

                '''
                    处理写回指令
                '''
                if inst_obj.instruction.isMemoryWrite():
                    # gadget中的写回永远是最后一个 [.] 0x7fffe6281a9c: mov byte ptr [rax + rdx], sil
                    self.G1["src_location"] = inst_obj.instruction.getAddress()
                    tmp_op = inst_obj.instruction.getOperands()
                    if tmp_op[0].getType() == OPERAND.MEM:

                        if ctx.isMemoryTainted(tmp_op[0]):
                            value_taint = True
                        if 'unknown' not in str(tmp_op[0].getBaseRegister()):
                            self.G1['dst_reg']['base'] =  str(tmp_op[0].getBaseRegister()).split(':')[0]
                            if ctx.isRegisterTainted(tmp_op[0].getBaseRegister()):
                                dest_taint = True
                        if 'unknown' not in str(tmp_op[0].getIndexRegister()):
                            self.G1['dst_reg']['idx'] =  str(tmp_op[0].getIndexRegister()).split(':')[0]
                            if ctx.isRegisterTainted(tmp_op[0].getIndexRegister()):
                                dest_taint = True
                        # 这里的倍数能看到
                        self.G1['dst_reg']['imm1'] =  int(str(tmp_op[0].getScale()).split(':')[0], 16)
                        # 但是相加的立即数看不到 # TODO 这里遇到相应的指令之后再看
                        self.G1['dst_reg']['imm2'] =  twos_complement_to_int(str(tmp_op[0].getDisplacement()).split(':')[0])
                        self.G1["dst_location"] = inst_obj.instruction.getAddress()

                    else:
                        raise Exception("Not A Memory Write inst!!!")
                    
                    if tmp_op[-1].getType() == OPERAND.REG:
                        # 这里向上找从哪里load出来的
                        write_data_op = tmp_op

                elif inst_obj.instruction.isMemoryRead():
                    '''
                        这里处理读出指令
                    '''
                    tmp_op = inst_obj.instruction.getOperands()
                    # if tmp_op[-1].getType() == OPERAND.MEM:
                    #     print(tmp_op[-1].getIndexRegister())
                    #     print(tmp_op[-1].getBaseRegister())
                    #     print(tmp_op[-1].getScale())
                    
                    # 这里检查左操作数是否是最终写入目标地址的数据，如果是则直接取出其读指针
                    if tmp_op[0].getType() == OPERAND.REG and write_data_op is not None:
                        if is_op_equal(str(write_data_op[-1]).split(':')[0], str(tmp_op[0]).split(':')[0]):
                            # 这里找到是何时读入的,如果是这里的就将这里视为最终地址
                            if 'unknown' not in str(tmp_op[-1].getBaseRegister()):
                                self.G1['src_reg']['base'] =  str(tmp_op[-1].getBaseRegister()).split(':')[0]
                                if ctx.isRegisterTainted(tmp_op[-1].getBaseRegister()):
                                    src_taint = True
                            if 'unknown' not in str(tmp_op[-1].getIndexRegister()):
                                self.G1['src_reg']['idx'] =  str(tmp_op[-1].getIndexRegister()).split(':')[0]
                                if ctx.isRegisterTainted(tmp_op[-1].getIndexRegister()):
                                    src_taint = True
                            # if src_taint is False:
                            #     # 这里证明源地址不受污染，那就求解源数据的取值范围
                            self.G1["src_data_reg"]["base"] = str(write_data_op[-1]).split(':')[0]
                            self.G1["src_data_location"] = inst_obj.instruction.getAddress()
                            # 这里的倍数能看到
                            self.G1['src_reg']['imm1'] =  int(str(tmp_op[-1].getScale()).split(':')[0], 16)
                            # 但是相加的立即数看不到 # TODO 这里遇到相应的指令之后再看
                            self.G1['src_reg']['imm2'] =  twos_complement_to_int(str(tmp_op[-1].getDisplacement()).split(':')[0])


                            if  is_op_equal(str(tmp_op[0]).split(':')[0] , str(tmp_op[-1].getBaseRegister()).split(':')[0]) or\
                                is_op_equal(str(tmp_op[0]).split(':')[0] , str(tmp_op[-1].getIndexRegister()).split(':')[0]):
                                for i in range(len(self.serial_list)):
                                    if self.serial_list[i] == inst_obj.instruction.getAddress():
                                        self.G1["src_location"] = self.serial_list[i-1]
                            else:
                                self.G1["src_location"] = inst_obj.instruction.getAddress()
                        
                else:
                    '''
                        mov 或者运算指令，如果是mov指令则可能要将write_data_op进行替换
                    '''
                    import os
                    os.system("echo "+str(inst_obj.instruction) + "> WRONG_INST.txt")
            new_gadget.instructions.reverse()
        
        
        if dest_taint is True and 'memset' in new_gadget.gadget_type:
            self.G1["target_type"] = "AMW"
        elif dest_taint is True:
            if src_taint is True:
                self.G1["target_type"] = "AMC" # 1 1 x
            elif value_taint is True:
                self.G1["target_type"] = "AMW" # 1 0 1
            else:
                self.G1["target_type"] = "SVW" # 1 0 0 源地址和源内容都无法改变 State Value Write
        elif src_taint is True:
            if 'RECV' in new_gadget.gadget_type:
                self.G1["target_type"] = "AMW"
            else:
                self.G1["target_type"] = "AMR" # 0 1 x
        else:
            self.G1["target_type"] = "USELESS" # 0 0 x
            # 这里直接return，不进行任何的操作
            return

        global SAVED_DIR
        self.seq_num += 1
        self.G1["target_id"] = self.seq_num
        self.G1["source_adr"] = self.G1["serial"][0]
        self.G1["target_adr"] = self.G1["serial"][-1]
        if 'RECV' not in new_gadget.gadget_type and 'memset' not in new_gadget.gadget_type:
            if self.G1["dst_reg"]["base"] is None or  self.G1["src_reg"]["base"] is None:
                print("EROOR FOUND REG")
                return
        
            if 'sp' in self.G1["dst_reg"]["base"] or 'sp' in self.G1["src_reg"]["base"]:
                print("VARIABLE SEND")
                return
            # raise Exception("EROOR FOUND REG")
        # 将对象保存到JSON文件
        with open(SAVED_DIR+"/"+file_name+'_'+hashlib.sha256(str(time.time()).encode()).hexdigest()+".json", 'w') as f:
            # print(self.G1)
            # print(loop_taint)
            json.dump([self.G1], f, indent=4)
        # 清理当前Gadget的信息
        self.clearG1()
        print("New Gadget saved in",SAVED_DIR+"/"+file_name+'_'+hashlib.sha256(str(time.time()).encode()).hexdigest()+".json")
    # 加载json数据
    def load_json(self, file_name):
        with open(file_name, 'r') as f:
            loaded_data = json.load(f)
        return loaded_data