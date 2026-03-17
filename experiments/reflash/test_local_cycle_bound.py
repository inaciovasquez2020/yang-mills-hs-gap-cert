import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def ball_subgraph(G,v,R):
    nodes = nx.single_source_shortest_path_length(G,v,cutoff=R).keys()
    return G.subgraph(nodes).copy()

def local_cycle_bound(G,R):
    bounds=[]
    for v in G.nodes():
        H = ball_subgraph(G,v,R)
        bounds.append(cycle_rank(H))
    return max(bounds)

def torus_graph(n):
    G = nx.grid_2d_graph(n,n,periodic=True)
    return nx.convert_node_labels_to_integers(G)

for n in [6,8,10]:
    G = torus_graph(n)
    global_rank = cycle_rank(G)
    local_bound = local_cycle_bound(G,2)
    print("n",n,"global_rank",global_rank,"local_bound",local_bound)
