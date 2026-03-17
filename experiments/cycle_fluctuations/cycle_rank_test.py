import networkx as nx
from experiments.block_graph.build_block_graph import build_block_graph

G = build_block_graph(6,6)

rank = G.number_of_edges() - G.number_of_nodes() + nx.number_connected_components(G)

print("cycle rank:", rank)

basis = nx.cycle_basis(G)

print("basis size:", len(basis))
