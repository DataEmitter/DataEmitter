import angr
import dill
import time
import sys
from path_controller.smart_sort import build_map
import config.__config as cn
from config.__config import *
import pickle
from utils.tool_lib import is64Arch
import os

DUMP = True
LOAD = False
bin_path = "../samples/binary/libgstflxdec.so"
dump_path = "../samples/dump/gstreamer.dump"

bin_name = bin_path.split("/")[-1]
print("Analyse", bin_name)
if not os.path.exists('./MidResult/'+bin_name+'/'):
    os.mkdir('./MidResult/'+bin_name+'/')

if ".so" not in bin_path:
    cn.IS_LIB = False

if is64Arch(bin_path):
    cn.ANALYSE_MODE = X86_64
    cn.ANGR_BASE =  0x400000
else:
    cn.ANALYSE_MODE = X86_32
    cn.ANGR_BASE = 0x8048000


def show_time(start_time):
    end_time = time.time()
    run_time = end_time - start_time    
    # 将运行时间转换为时分秒格式
    hours = int(run_time // 3600)
    minutes = int((run_time % 3600) // 60)
    seconds = int(run_time % 60)

    # 打印运行时间
    print(f"Finished in  {hours}h {minutes}m {seconds}s")
sys.setrecursionlimit(10000) 
start_time = time.time()
print("+++++++++ Start Reading Dump +++++++++")
entry_point = None
code_base_adr = None
with open(dump_path,'rb') as file:
    print("Open Success")
    dump_data = pickle.load(file,encoding='iso-8859-1')
    regs = dump_data[0]
    codes = dump_data[2]
    #  读取程序的起始点
    if 'rip' in regs:
        entry_point = regs['rip']
    else:
        entry_point = regs['eip']
    for code in codes:
        if bin_name[:-1] in code['name']:
            code_base_adr = code['start']

show_time(start_time)

print("+++++++++ Start Extracting ANGR_PROJ +++++++++")
if LOAD:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.angr_proj', 'rb') as f:
        angr_proj=dill.load(f)
else:
    if cn.ANALYSE_MODE == 1:
        angr_proj=angr.Project(bin_path, arch='x86_64',auto_load_libs=False,load_options={'main_opts': {'base_addr': cn.ANGR_BASE}})
    else:
        '''
            这里应该还是32位
        '''
        angr_proj=angr.Project(bin_path, arch='x86',auto_load_libs=False,load_options={'main_opts': {'base_addr': cn.ANGR_BASE}})

if DUMP:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.angr_proj', 'wb') as f:
        dill.dump(angr_proj, f)
show_time(start_time)

print("+++++++++ Start Extracting CFG +++++++++")
if LOAD:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.cfg_model', 'rb') as f:
        cfg = dill.load(f)
else:
    cfg = angr_proj.analyses.CFGFast()
if DUMP:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.cfg_model', 'wb') as f:
        dill.dump(cfg, f)
show_time(start_time)

print("+++++++++ Start Extracting LOOP +++++++++")
if LOAD:
    try:
        with open('./MidResult/'+bin_name+'/'+bin_name + '.looplist', 'wb') as f:
            loop_list=dill.load(f)
    except:
        loop_list=angr_proj.analyses.LoopFinder().loops
else:
# 提取loop
    loop_list=angr_proj.analyses.LoopFinder().loops
    
if DUMP:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.looplist', 'wb') as f:
        dill.dump(loop_list, f)
# 
print("+++++++++ Start Building BRANCH_MAP +++++++++")
BRANCH_MAP,angr_cfg,angr_proj = build_map(bin_path=bin_path, 
                                          code_base= code_base_adr, 
                                          start_position = entry_point,
                                          search_depth=SEARCH_DEPTH,
                                          cfg_model=cfg,
                                          loop_list =loop_list,
                                          angr_proj= angr_proj)
if DUMP:
    with open('./MidResult/'+bin_name+'/'+bin_name + '.BRANCH_MAP', 'wb') as f:
        dill.dump(BRANCH_MAP, f)
show_time(start_time)
