import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def ball_subgraph(G, v, R):
    nodes = nx.single_source_shortest_path_length(G, v, cutoff=R).keys()
    return G.subgraph(nodes).copy()

def localized_cycle_basis(G, v, R):
    H = ball_subgraph(G, v, R)
    basis = nx.cycle_basis(H)
    return H, basis

def torus(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def run():
    G = torus(8)
    for v in [0, 1, 9]:
        H, basis = localized_cycle_basis(G, v, 2)
        print("center", v)
        print("local_nodes", H.number_of_nodes())
        print("local_edges", H.number_of_edges())
        print("local_cycle_rank", cycle_rank(H))
        print("basis_size", len(basis))
        print("")

if __name__ == "__main__":
    run()
