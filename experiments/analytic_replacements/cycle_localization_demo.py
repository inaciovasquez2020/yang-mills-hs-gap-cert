import networkx as nx

G = nx.grid_2d_graph(20,20)

cycle = [(5,5),(5,6),(6,6),(6,5)]

neighborhood=set()

for v in cycle:
    neighborhood.update(nx.single_source_shortest_path_length(G,v,2).keys())

print("cycle size:",len(cycle))
print("localized support size:",len(neighborhood))
