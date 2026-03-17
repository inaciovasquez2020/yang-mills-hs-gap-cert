import numpy as np
import networkx as nx

def build_grid_graph(n):
    G = nx.grid_2d_graph(n,n)
    G = nx.convert_node_labels_to_integers(G)
    return G

def laplacian_gap(G):
    L = nx.laplacian_matrix(G).todense()
    eig = np.linalg.eigvals(L)
    eig = np.sort(np.real(eig))
    return eig[1]

if __name__ == "__main__":
    for n in [4,6,8,10]:
        G = build_grid_graph(n)
        gap = laplacian_gap(G)
        print("grid:",n,"laplacian gap:",gap)
