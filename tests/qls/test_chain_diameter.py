import networkx as nx

def ball(G,v,R):
    nodes = nx.single_source_shortest_path_length(G,v,cutoff=R).keys()
    return G.subgraph(nodes)

def test_chain_diameter():
    G = nx.grid_2d_graph(8,8,periodic=True)
    G = nx.convert_node_labels_to_integers(G)

    R = 2
    diameters = []

    for v in G.nodes():
        H = ball(G,v,R)
        diameters.append(nx.diameter(H))

    assert max(diameters) <= 4
