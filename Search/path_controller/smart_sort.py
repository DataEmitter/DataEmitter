'''
    该模块记录当前的排序算法
'''
from path_controller.static_analyse import *
# from threading import Thread
import multiprocessing
import inspect
from time import time,sleep
from operator import itemgetter
import config.__config as cn
import traceback
def get_call_depth():
    current_thread_traceback = traceback.extract_stack()
    call_stack_length = len(current_thread_traceback)
    return call_stack_length

'''
    该类设置一个二进制程序中的起始位置和终点位置，构造一张程序中涉及到的边的权重，进行反向传播，附加权重
'''
class smart_builder(multiprocessing.Process):
    def __init__(self,
                 start_position, # 程序分析的入口地址
                 code_base, # 程序镜像基地址
                 proc_id, # 设置当前程序的线程id
                 angr_proj, #  angr proj对象
                 binary_path , # 当前程序二进制文件的路径
                 position_obj,
                 cfg,
                 result_queue, # 用于进程通信
                 call_depth = 20,
                 ) -> None:
        multiprocessing.Process.__init__(self) # 进程初始化
        '''
            衰减参数
        '''
        self.back_ward_param = 0.7 # 反向传播传导参数
        self.fresh_param = 0.9 # 正向执行的过程中导致的路径价值衰减参数
        self.max_call_depth = call_depth # 单次递归最大深度
        '''
            外部传入变量
        '''
        self.result_queue = result_queue
        self.start_position = start_position
        self.thread_id = proc_id
        self.code_base = code_base
        self.angr_proj = angr_proj
        self.binary_path = binary_path
        self.position_obj = position_obj # 记录当前每个高价值点所处的位置

        '''
            中间分析临时变量
        '''
        # 存储中间分析结果
        self.edge_table = {} # {edge: rank},记录反向传播中每一个边的得分，（addr_end, addr_start）: rank
        self.last_inst_table = {} # 和上面的操作没有区别，只是用来存储最后一条指令到下一个block第一条指令的映射
        # 记录已经到达过的结点
        self.touched_node = {}
        self.cfg = cfg
        self.start_block = None
        self.end_block = None
        self.touched_start = False
        self.run_flag = False

    def reverse_search(self,end_block, block_score):
        if get_call_depth() > self.max_call_depth:
            return
        # 这里暂存一个变量，用于进行动态参数衰减
        tmp_backward_param = self.back_ward_param
        '''
            动态衰减策略，如果是只有一个结点直来直往就不进行衰减
        '''
        if end_block is None:
            return
        if len(end_block.predecessors) == 1:
            tmp_backward_param = 1
        for pre_block in end_block.predecessors:

            #  检查是否到达了出发点
            if pre_block.addr == self.start_position - self.code_base + cn.ANGR_BASE:
                self.touched_start = True
                
            self.edge_table[(end_block.addr, pre_block.addr)] = block_score * tmp_backward_param
            
            self.touched_node[pre_block.addr] = 0

            for per_edge in self.edge_table:
                if per_edge[-1] == pre_block.addr:

                    if  self.edge_table[per_edge] > self.touched_node[pre_block.addr]:
                        self.touched_node[pre_block.addr] = self.edge_table[per_edge]

        for pre_block in end_block.predecessors:
            # 在衰减后向上进行探索
            self.reverse_search(pre_block, block_score=self.touched_node[pre_block.addr] * tmp_backward_param)


    def run(self):
        start_time = time()
        if IS_LIB: # 这里针对lib库进行一次单独的操作
            self.end_block = self.cfg.get_any_node(self.position_obj.addr)
        else:
            self.end_block = self.cfg.get_any_node(self.position_obj.addr - self.code_base + cn.ANGR_BASE)
        self.start_block = self.cfg.get_any_node(self.start_position - self.code_base + cn.ANGR_BASE)
        # 如果找不到相应的起止位置，则打印错误信息
        if self.end_block is None:
            block = self.angr_proj.factory.block(self.position_obj.addr)
            function_manager = self.cfg.kb.functions
            # 遍历所有函数
            try:
                for function in function_manager.values():
                    # 检查给定地址是否在函数的地址范围内
                    for block in function.blocks:
                        if self.position_obj.addr in block.instruction_addrs:
                            self.end_block = block
                            break
                    if self.end_block is not None:
                        break
            except:
                return
            self.end_block = self.cfg.get_any_node(self.end_block.addr)
        if self.start_block is None:
            # 这里说明可能是使用objdump搞的，那么就直接使用原本的地址尝试
            # 这里有个问题，就是获取的指令地址并不是基本块的开头
            if IS_LIB:
                block = self.angr_proj.factory.block(self.start_position - self.code_base + cn.ANGR_BASE)
            else:
                block = self.angr_proj.factory.block(self.start_position)
            function_manager = self.cfg.kb.functions
            # 遍历所有函数
            for function in function_manager.values():
                # 检查给定地址是否在函数的地址范围内
                for block in function.blocks:
                    if self.start_position in block.instruction_addrs:
                        self.start_block = block
                        break
                if self.start_block is not None:
                    break
            self.start_block = self.cfg.get_any_node(self.start_block.addr)
        
        self.reverse_search(self.end_block, TYPE_RANK[self.position_obj.type])
        #  将计算结果放回
        
        # 这里对switch_node 做二次处理,保证switch的
        if self.position_obj.type == 'switch':

            try:
                for next_node in self.end_block.successors:
                    if  (self.end_block.addr,next_node.addr) not in self.edge_table:
                        self.edge_table[(next_node.addr, self.end_block.addr)] = TYPE_RANK[self.position_obj.type]
                    else:
                        self.edge_table[(next_node.addr, self.end_block.addr)] += TYPE_RANK[self.position_obj.type]
            except:
                print("[-] No Successors")
        # 这里根据基本块首地址获得最后一条指令的地址，构造新的边
        for per_edge in self.edge_table:
            # 出度块首地址，需要转换为最后一条边的地址
            pre_block_addr = per_edge[-1]
            # 入度块地址
            next_block_addr = per_edge[0]
            pre_block = self.cfg.get_any_node(pre_block_addr)
            if pre_block.block is None:
                # print(hex(pre_block_addr))
                continue
            # 获取最后一个块的地址,存入到新的映射表中去,在这里转正了
            self.last_inst_table[(pre_block.block.capstone.insns[-1].address,next_block_addr)] = self.edge_table[per_edge]
        self.edge_table = self.last_inst_table
        print("thread:",self.thread_id,"finished in", time() - start_time ,"s -->",len(self.last_inst_table))
        self.run_flag = True
        self.result_queue.put(self.get_result())

    def get_result(self):
        if not self.run_flag:
            raise Exception("NO!",self.thread_id)
        if len(self.edge_table) == 0:
            print("Got Nothing")
        else:
            print("yep!")
        return self.edge_table
23


def build_map(bin_path,
              code_base,
            start_position,
            search_depth = 20,
            cfg_model = None,
            loop_list = None,
            angr_proj = None):

    obj_list,angr_proj,cfg = static_extract_local_features(start_position,bin_path, cn.ANALYSE_MODE,cfg_model,loop_list,angr_proj)
    proc_base_id = 0
    procs_bucket = []
    tmp_bucket = []
    result_queue = multiprocessing.Queue()
    thread_counter = 0
    print("Trying to Solve", len(obj_list), "thread!")
    for per_position in obj_list:
        new_builder = smart_builder(
            code_base= code_base,
            start_position = start_position,
            position_obj = per_position,
            proc_id = proc_base_id,
            cfg = cfg_model,
            binary_path = bin_path,
            angr_proj = angr_proj,
            result_queue = result_queue,
            call_depth=search_depth,
        )
        new_builder.start()
        procs_bucket.append(new_builder)
        thread_counter += 1
        # new_builder.join()
        proc_base_id += 1
        if thread_counter > 4:#这里算15个线程一起
            # 主线程等待100秒，等待所有线程搜索结束
            print("Main Thread Waitting For All Threads....")
            for proc in procs_bucket:
                proc.join()
                del proc
                # tmp_bucket.append(proc)
            print("Finish Waitting...")
            thread_counter = 0
            procs_bucket = []
        

    print("All Threads Finished!")
    final_result = {}
    count_table = {} 
    while not result_queue.empty():
        if final_result is None:
            final_result  = result_queue.get()
        else:
            tmp_result = result_queue.get()
            for per_node in tmp_result:

                if per_node in count_table:
                    count_table[per_node] += 1
                elif per_node not in final_result:
                    count_table[per_node] = 1
                else:
                    count_table[per_node] = 2

                if per_node in final_result:
                    final_result[per_node] += tmp_result[per_node]
                else:
                    # 如果不在就直接赋值
                    final_result[per_node] = tmp_result[per_node]
                # 检查
    # 取均值处理
    for per_edge in final_result:
        final_result[per_edge] = final_result[per_edge] / count_table[per_edge]

    return final_result,cfg,angr_proj

# 获取当前分支的价值
def get_rank_from_map(rank_map, # 分支价值
                      start_addr, # 上一条指令
                      end_addr, # 当前指令
                      ctx,
                      code_base, # 当前程序的代码基址
                      ):
    '''
        这里不应该是传入的指令地址直接进行比对，而是根据指令地址找到相应的block进行比较
    '''
    now_edge = (start_addr - code_base + cn.ANGR_BASE, end_addr - code_base + cn.ANGR_BASE)
    if now_edge in rank_map:
        return rank_map[now_edge]
    else:
        return 0

# 依照rank进行排序
def sort_by_rank(thread_pathes):
    # 从大到小进行排序
    sorted_dict = dict(sorted(thread_pathes.items(), key=lambda item: item[0][1], reverse=True))
    return sorted_dict
    