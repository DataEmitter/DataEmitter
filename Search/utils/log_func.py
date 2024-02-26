from config.__config import *
# 该文件用于进行对文件进行输出
ANGR_BASE = 0x400000
# 该函数用于对错误进行输出
def ERROR_log(error_msg:str,DEBUG:bool):
    if DEBUG:
        print('\033[31m[-] %s \033[0m' % error_msg)

# 给函数用于进行对调试信息的输出
def DEBUG_log(log_msg:str,DEBUG:bool):
    print('\033[30m[+] %s \033[0m' % log_msg)

def RESULT_log(log_msg:str,TaintLabel:bool,thread_id = '.'):
    if DEBUG:
        if TaintLabel:
            print('\033[32m[%s] %s \033[0m' % (thread_id,log_msg))
        else:
            print('\033[90m[%s] %s \033[0m' % (thread_id,log_msg))
            # print('['+thread_id+']',log_msg)

def putConstrain(ctx):
    my_Cst  = ctx.getPathConstraints()
    print("++++++++++++++++++++++++++++++++++++++++")
    for cst in my_Cst:
        print("=====================================")
        print("Comment:",cst.getComment())
        # print(cst.getTakenAddress())
        print("TakenPredicate",cst.getTakenPredicate())
    
def show_framework_result(gadget_manager,gdt_save_path, dis_save_path):
    with open(gdt_save_path,'w') as fd: 
        fd.writelines("Show Gadgets")
        RESULT_log("Show Gadgets:",True)
        for gdt in gadget_manager.analyser_manager.gdt_mode_list:
            print('----------------------------------')
            fd.writelines("----------------------------------")
            print("Type:",gdt.gadget_type,"---->",gdt.gdt_attribute)
            fd.writelines("Type: "+gdt.gadget_type+" ----> "+ str(gdt.gdt_attribute))
            for st in gdt.instructions:
                fd.writelines(str(st.instruction))
                print(st.instruction)
            print("\nPath to Gadget:",gdt.jmp_path) # 输出当前通往gadget的跳转路径 
            fd.writelines("\nPath to Gadget: "+str(gdt.jmp_path))
            if gdt.enhancer is not None:
                print("\nEnhancer:",gdt.enhancer)
                fd.writelines("\nEnhancer: "+ str(gdt.enhancer))
    print("\n\n")
    with open(dis_save_path,'w') as fd:
        RESULT_log("Real Disapatcher:",True)
        fd.writelines("Real Disapatcher:")
        for disp in gadget_manager.real_dispatcher:
            print("Dispatcher:", hex(disp))
            fd.writelines("Dispatcher: "+ hex(disp))
            for idx, gdt in enumerate(gadget_manager.real_dispatcher[disp]):
                print("Gadget: ",idx+1)
                fd.writelines("Gadget: "+ str(idx+1))
                for inst in gdt.instructions:
                    print("------>  ", inst.instruction)
                    fd.writelines("------>  "+ str(inst.instruction))