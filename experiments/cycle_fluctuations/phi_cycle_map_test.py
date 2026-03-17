import numpy as np
import networkx as nx
from experiments.block_graph.build_block_graph import build_block_graph

def build_block_basis(num_blocks, block_size):
    psi = []
    for _ in range(num_blocks):
        v = np.random.randn(block_size)
        v = v - np.mean(v)
        psi.append(v)
    return psi

def phi_edge(psi_i, psi_j):
    return psi_i - psi_j

G = build_block_graph(5,5)

nodes = list(G.nodes())
node_index = {n:i for i,n in enumerate(nodes)}

psi = build_block_basis(len(nodes),20)

cycles = nx.cycle_basis(G)

cycle_vectors = []

for c in cycles:
    v = np.zeros(20)
    for i in range(len(c)):
        a = node_index[c[i]]
        b = node_index[c[(i+1)%len(c)]]
        v += phi_edge(psi[a],psi[b])
    cycle_vectors.append(v)

print("constructed cycle vectors:", len(cycle_vectors))
print("vector dimension:", len(cycle_vectors[0]))
