import networkx as nx

def ball(G,v,R):
    nodes = nx.single_source_shortest_path_length(G,v,cutoff=R).keys()
    return G.subgraph(nodes)

def diameter(G):
    return nx.diameter(G)

def torus(n):
    G = nx.grid_2d_graph(n,n,periodic=True)
    return nx.convert_node_labels_to_integers(G)

R = 2

for n in [6,8,10]:
    G = torus(n)
    dvals = []
    for v in G.nodes():
        H = ball(G,v,R)
        dvals.append(diameter(H))
    print("n",n,"max_local_diameter",max(dvals))
