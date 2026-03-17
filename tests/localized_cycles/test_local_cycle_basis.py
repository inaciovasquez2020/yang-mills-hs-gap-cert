import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def ball_subgraph(G, v, R):
    nodes = nx.single_source_shortest_path_length(G, v, cutoff=R).keys()
    return G.subgraph(nodes).copy()

def torus(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def test_local_cycle_basis_matches_rank():
    G = torus(8)
    H = ball_subgraph(G, 0, 2)
    basis = nx.cycle_basis(H)
    assert len(basis) == cycle_rank(H)
