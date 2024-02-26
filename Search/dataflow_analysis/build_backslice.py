
from networkx import DiGraph

def plot_backslice(backslice, fname, format="png"):
    vis = AngrVisFactory().default_common_graph_pipeline(type=True)
    vis.set_output(DotOutput(fname, format=format))
    vis.process(backslice)

def create_subgraph(G,target_node,subgraph_nodes):
    for n in G.predecessors(target_node):
        subgraph_nodes.append(n)
        screate_subgraph(G,n,subgraph_nodes)

def Generate_Backslice(dfg, target_node, flag=0):
    subgraph_nodes = []
    subgraph_nodes.append(target_node)
    create_subgraph(dfg,target_node,subgraph_nodes)
    backslice = dfg.subgraph(subgraph_nodes)
    if flag:
        plot_backslice(backslice, "backslice_%s"%str(target_node), format="png") 
    return backslice

def simplify_backslice1(backslice,node):
    backslice = DiGraph(backslice)
    dfs_stack = []
    dfs_stack.append(node)
    visited = set()
    while len(dfs_stack)!=0:
        flag=0
        current_node = dfs_stack.pop()
        visited.add(current_node)
        pre_nodes = list(backslice.predecessors(current_node))
        if len(pre_nodes)==0:
            continue
        exprs = list(current_node.expressions)
        if current_node.tag == 'Ist_WrTmp':
            if exprs[0].tag == 'Iex_RdTmp': # 
                flag=1
                tmp = current_node.tmp #
        if flag:
            for pre_node in pre_nodes:
                predecessors_nodes = backslice.predecessors(pre_node)
                successors_nodes = backslice.successors(pre_node)
                backslice.remove_node(pre_node)
                tmp_node = pre_node
                tmp_node.tmp = tmp
                backslice.add_node(tmp_node)
                for predecessors_node in predecessors_nodes:
                    backslice.add_edge(predecessors_node,tmp_node)
                for successors_node in successors_nodes:
                    backslice.add_edge(tmp_node,successors_node)
        for pre_node in pre_nodes: 
            if pre_node not in visited:
                dfs_stack.append(pre_node)
    return backslice

def simplify_backslice2(backslice,simplified_backslice,node):
    dfs_stack = []
    dfs_stack.append(node)
    visited = set()
    simplified_backslice.add_node(node) 
    while len(dfs_stack)!=0:
        flag=1
        current_node = dfs_stack.pop()
        visited.add(current_node)
        pre_nodes = list(backslice.predecessors(current_node))
        if len(pre_nodes)==0:
            continue
        exprs = list(current_node.expressions)
        if current_node.tag == 'Ist_WrTmp':
            if exprs[0].tag == 'Iex_RdTmp': # 类似赋值操作t1=t2
                flag=0
        
        for pre_node in pre_nodes:
            if pre_node not in visited:
                dfs_stack.append(pre_node)
            if flag:
                simplified_backslice.add_edge(pre_node,current_node)
            else:
                new_pre_node = copy.copy(pre_node)
                for successors_node in list(simplified_backslice.successors(current_node)):
                    simplified_backslice.add_edge(new_pre_node,successors_node)
                simplified_backslice.remove_node(current_node)

def Generate_simplified_backslice(backslice,target_node,flag=0):
    simplified_backslice = DiGraph() # 解冻,否则remove_node时会报错
    # 修改待删除节点的父节点的tmp值
    backslice = simplify_backslice1(backslice,target_node)
    # 删除无意义节点
    simplify_backslice2(backslice,simplified_backslice,target_node)
    if flag:
        plot_backslice(simplified_backslice, "simplified_backslice_%s"%target_node, format="png") 
    return simplified_backslice

def find_all_source(backslice,target_node):
    source_nodes = [] 
    dfs_stack = [] 
    visited = set() 
    dfs_stack.append(target_node) 
    while len(dfs_stack)!=0:
        current_node = dfs_stack.pop()
        visited.add(current_node)
        pre_nodes = list(backslice.predecessors(current_node))
        if len(pre_nodes)==0:
            if current_node.tag == 'Iex_Const':
                suc_nodes = list(backslice.successors(current_node))
                for suc_node in suc_nodes:
                    if suc_node not in source_nodes:
                        source_nodes.append(suc_node)
            else:
                source_nodes.append(current_node)
        else:
            for pre_node in pre_nodes: 
                if pre_node not in visited:
                    dfs_stack.append(pre_node)
    return source_nodes