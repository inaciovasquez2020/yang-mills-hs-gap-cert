import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

for n in [6,8,10,12,14]:
    G = nx.grid_2d_graph(n,n)
    r = cycle_rank(G)
    print("grid",n,"cycle_rank",r)
