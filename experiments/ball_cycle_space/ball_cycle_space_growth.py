import networkx as nx

def ball_subgraph(G, v, R):
    nodes = nx.single_source_shortest_path_length(G, v, cutoff=R).keys()
    return G.subgraph(nodes).copy()

def cycle_rank(H):
    return H.number_of_edges() - H.number_of_nodes() + nx.number_connected_components(H)

def torus_graph(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def theoretical_vertex_bound(delta, R):
    if delta == 1:
        return R + 1
    s = 0
    for j in range(R + 1):
        s += delta ** j
    return s

def run():
    G = torus_graph(30)
    delta = max(dict(G.degree()).values())
    v = 0

    print("R,|V(B_R)|,|E(B_R)|,cycle_rank,theoretical_vertex_bound,delta^(R+1)")
    for R in range(1, 7):
        H = ball_subgraph(G, v, R)
        V = H.number_of_nodes()
        E = H.number_of_edges()
        Z1 = cycle_rank(H)
        tvb = theoretical_vertex_bound(delta, R)
        crude = delta ** (R + 1)
        print(f"{R},{V},{E},{Z1},{tvb},{crude}")

if __name__ == "__main__":
    run()
