import networkx as nx

def cycle_rank(G):
    return G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

def ball(G,v,R):
    nodes = nx.single_source_shortest_path_length(G,v,cutoff=R).keys()
    return G.subgraph(nodes).copy()

def bound_estimate(G,R):
    vals=[]
    for v in G.nodes():
        H=ball(G,v,R)
        vals.append(cycle_rank(H))
    return max(vals)

def torus(n):
    G=nx.grid_2d_graph(n,n,periodic=True)
    return nx.convert_node_labels_to_integers(G)

for n in [6,8,10]:
    G=torus(n)
    print("n",n,"local_bound_R2",bound_estimate(G,2))
