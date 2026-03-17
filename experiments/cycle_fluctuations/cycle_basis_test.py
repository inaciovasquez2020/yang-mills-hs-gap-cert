import networkx as nx
from experiments.block_graph.build_block_graph import build_block_graph

G = build_block_graph(6,6)

cycles = nx.cycle_basis(G)

print("cycle basis size:", len(cycles))

for c in cycles[:5]:
    print("cycle:", c)
