import networkx as nx

def ball_subgraph(G, v, R):
    nodes = nx.single_source_shortest_path_length(G, v, cutoff=R).keys()
    return G.subgraph(nodes).copy()

def cycle_rank(H):
    return H.number_of_edges() - H.number_of_nodes() + nx.number_connected_components(H)

def torus_graph(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def run():
    G = torus_graph(20)
    R = 2
    print("v,|V|,|E|,cycle_rank")
    for v in [0, 1, 20, 21, 42]:
        H = ball_subgraph(G, v, R)
        print(f"{v},{H.number_of_nodes()},{H.number_of_edges()},{cycle_rank(H)}")

if __name__ == "__main__":
    run()
