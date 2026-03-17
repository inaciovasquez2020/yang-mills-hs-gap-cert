import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def run():
    G = nx.grid_2d_graph(5,5)
    rank = cycle_rank(G)
    print("cycle rank:", rank)

run()
