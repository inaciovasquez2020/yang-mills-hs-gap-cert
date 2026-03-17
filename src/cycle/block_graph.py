import networkx as nx

def build_block_graph(nx_blocks, ny_blocks):
    G = nx.Graph()
    for i in range(nx_blocks):
        for j in range(ny_blocks):
            G.add_node((i,j))
    for i in range(nx_blocks):
        for j in range(ny_blocks):
            if i+1 < nx_blocks:
                G.add_edge((i,j),(i+1,j))
            if j+1 < ny_blocks:
                G.add_edge((i,j),(i,j+1))
    return G
