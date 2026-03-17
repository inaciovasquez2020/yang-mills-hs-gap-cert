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

def run():
    G = torus(8)

    localized_nodes = [0, 1, 2, 8, 9]
    ok, center = localized_in_some_ball(G, localized_nodes, 2)
    print("localized_nodes:", localized_nodes)
    print("localized:", ok, "center:", center)

    spread_nodes = [0, 7, 32, 63]
    ok2, center2 = localized_in_some_ball(G, spread_nodes, 2)
    print("spread_nodes:", spread_nodes)
    print("localized:", ok2, "center:", center2)

if __name__ == "__main__":
    run()
