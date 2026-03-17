import numpy as np
import networkx as nx
from experiments.block_graph.build_block_graph import build_block_graph

G = build_block_graph(5,5)
cycles = nx.cycle_basis(G)

dim = len(cycles)

M = np.random.randn(dim,dim)

rank = np.linalg.matrix_rank(M)

print("cycle basis dimension:", dim)
print("random image rank:", rank)
