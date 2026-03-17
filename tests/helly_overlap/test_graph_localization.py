import networkx as nx

def ball_nodes(G, v, R):
    return set(nx.single_source_shortest_path_length(G, v, cutoff=R).keys())

def localized_in_some_ball(G, nodes, R):
    node_set = set(nodes)
    for v in G.nodes():
        if node_set.issubset(ball_nodes(G, v, R)):
            return True, v
    return False, None

def torus(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def test_graph_localization():
    G = torus(8)
    ok, _ = localized_in_some_ball(G, [0, 1, 2, 8, 9], 2)
    assert ok

def test_graph_nonlocalization():
    G = torus(8)
    ok, _ = localized_in_some_ball(G, [0, 7, 32, 63], 2)
    assert not ok
