import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def ball(G,v,R):
    nodes = nx.single_source_shortest_path_length(G,v,cutoff=R).keys()
    return G.subgraph(nodes)

def test_cycle_bound():
    G=nx.grid_2d_graph(8,8,periodic=True)
    G=nx.convert_node_labels_to_integers(G)

    global_rank=cycle_rank(G)

    bounds=[]
    for v in G.nodes():
        bounds.append(cycle_rank(ball(G,v,2)))

    assert max(bounds) < global_rank
