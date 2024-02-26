binary_path = "../samples/binary/libgstflxdec.so"
binary_name = binary_path.split('/')[-1]
dump_path = "../samples/dump/gstreamer.dump" 

Print_Payload = False

Check_Stitch = False

Activated = False

ANALYSE_MODE = "X64"
BITNESS = 64

tainted_mem = {
    0x7fffd0025960: 0x200,
    0x7fffd00231b0: 0x2
}

vsa_target_in = \
[
    {
        "target_id": 1, 
        "target_type": "AMW", 
        "source_adr": 0x7fffe62816f5, 
        "target_adr": 0x7fffe6281a9c, 
        "target_count":1, 
        "dst_reg": {'base':'rax','idx':'rdx','imm1':1,'imm2':0},
        "dst_location": 0x7fffe6281a9c, 
        "src_reg": {'base':'rcx','idx':'rdx','imm1':1,'imm2':0}, 
        "src_location": 0x7fffe6281a9c, 
        "len_reg":{'base':'rdi','idx':None,'imm1':1,'imm2':0}, 
        "len_location": 0x7fffe6281a9c, 
        "dst_value": None, 
        "src_value": None, 
        "src_mem_value": None, 
        "len_value":None, 
        "serial":[], 
        "activated":True 
    },
    {
        "target_id":3, 
        "target_type": "AMR", 
        "source_adr":0x7fffe6281a9c, 
        "target_adr":0x7fffe6281a0a, 
        "target_count":1, 
        "dst_reg":{'base':'rdi','idx':None,'imm1':1,'imm2':0}, 
        "dst_location": 0x7fffe6281a0a,
        "src_reg":{'base':'rsi','idx':None,'imm1':1,'imm2':0}, 
        "src_location": 0x7fffe6281a0a,
        "len_reg":{'base':'rdx','idx':None,'imm1':1,'imm2':0}, 
        "len_location": 0x7fffe6281a0a,
        "dst_value":None, 
        "src_value": None, 
        "src_mem_value": None, 
        "len_value":None, 
        "serial":[],
        "activated":False
    },
    {
        "target_id":4, 
        "source_adr":0x7fffe62816f5, 
        "target_adr":0x7fffe628179c, 
        "target_count":1, 
        "dst_reg":{'base':'rdi','idx':None,'imm1':1,'imm2':0}, 
        "dst_location": 0x7fffe628179c,
        "src_reg":{'base':'rsi','idx':None,'imm1':1,'imm2':0}, 
        "src_location": 0x7fffe628179c,
        "len_reg":{'base':'rdx','idx':None,'imm1':1,'imm2':0}, 
        "len_location": 0x7fffe628179c,
        "dst_value":None, 
        "src_value":None, 
        "src_mem_value":None,
        "len_value":None, 
        "serial":[],
        "activated":False
    }
]