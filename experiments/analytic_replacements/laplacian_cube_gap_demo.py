import networkx as nx
import numpy as np

def grid_cube_graph(L, d=2):
    if d == 2:
        return nx.grid_2d_graph(L, L)
    raise ValueError("Only d=2 implemented")

def laplacian_gap(G):
    M = nx.laplacian_matrix(G).astype(float).toarray()
    ev = np.linalg.eigvalsh(M)
    ev.sort()
    return float(ev[1])

def run():
    print("L,gap,L^2*gap")
    for L in [4, 6, 8, 10, 12, 16]:
        G = grid_cube_graph(L, 2)
        gap = laplacian_gap(G)
        print(f"{L},{gap:.12f},{(L**2)*gap:.12f}")

if __name__ == "__main__":
    run()
