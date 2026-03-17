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

def test_ball_vertex_bound():
    G = torus_graph(30)
    delta = max(dict(G.degree()).values())
    v = 0

    for R in range(1, 6):
        H = ball_subgraph(G, v, R)
        assert H.number_of_nodes() <= theoretical_vertex_bound(delta, R)

def test_cycle_rank_formula():
    G = torus_graph(30)
    v = 0

    for R in range(1, 6):
        H = ball_subgraph(G, v, R)
        lhs = cycle_rank(H)
        rhs = H.number_of_edges() - H.number_of_nodes() + nx.number_connected_components(H)
        assert lhs == rhs

if __name__ == "__main__":
    test_ball_vertex_bound()
    test_cycle_rank_formula()
    print("ball cycle-space tests: PASS")
