import networkx as nx

G = nx.grid_2d_graph(30,30)

cycle = [(10,10),(10,11),(11,11),(11,10)]

support=set()

for v in cycle:
    support.update(nx.single_source_shortest_path_length(G,v,2).keys())

print("cycle vertices:",len(cycle))
print("localized support:",len(support))
