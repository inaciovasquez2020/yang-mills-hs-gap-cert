import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def rooted_ball_signature(G, v, R):
    nodes = nx.single_source_shortest_path_length(G, v, cutoff=R)
    H = G.subgraph(nodes.keys()).copy()
    labels = {u: i for i, u in enumerate(sorted(H.nodes(), key=lambda x: (nodes[x], str(x))))}
    H = nx.relabel_nodes(H, labels)
    root = labels[v]
    dist_profile = tuple(sorted(nodes.values()))
    deg_profile = tuple(sorted(dict(H.degree()).values()))
    return (H.number_of_nodes(), H.number_of_edges(), root, dist_profile, deg_profile)

def local_type_count(G, R):
    sigs = [rooted_ball_signature(G, v, R) for v in G.nodes()]
    return len(set(sigs))

def torus_graph(n):
    G = nx.grid_2d_graph(n, n, periodic=True)
    return nx.convert_node_labels_to_integers(G)

def test_torus_homogeneity_and_cycle_growth():
    ranks = []
    for n in [6, 8, 10]:
        G = torus_graph(n)
        assert local_type_count(G, 1) == 1
        assert local_type_count(G, 2) == 1
        ranks.append(cycle_rank(G))
    assert ranks[0] < ranks[1] < ranks[2]

if __name__ == "__main__":
    test_torus_homogeneity_and_cycle_growth()
    print("torus homogeneity test: PASS")
