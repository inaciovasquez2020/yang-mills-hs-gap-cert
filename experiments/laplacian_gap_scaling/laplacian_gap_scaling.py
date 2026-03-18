import networkx as nx
import numpy as np

def laplacian_gap(G):
    L = nx.laplacian_matrix(G).todense()
    w = np.linalg.eigvalsh(L)
    return sorted(w)[1]

for n in [6,8,10,12,14]:
    G = nx.grid_2d_graph(n,n)
    gap = laplacian_gap(G)
    print("n",n,"gap",gap)
