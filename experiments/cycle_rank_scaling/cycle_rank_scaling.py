import networkx as nx

def grid_cycle_rank(n):
    G = nx.grid_2d_graph(n,n)
    V = G.number_of_nodes()
    E = G.number_of_edges()
    C = nx.number_connected_components(G)
    return E - V + C

def run():
    for n in [4,6,8,10,12]:
        rank = grid_cycle_rank(n)
        print("grid",n,"cycle_rank",rank)

run()
