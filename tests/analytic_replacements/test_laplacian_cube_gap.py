import networkx as nx
import numpy as np

def grid_cube_graph(L):
    return nx.grid_2d_graph(L, L)

def laplacian_gap(G):
    M = nx.laplacian_matrix(G).astype(float).toarray()
    ev = np.linalg.eigvalsh(M)
    ev.sort()
    return float(ev[1])

def test_gap_inverse_square_window():
    vals = []
    for L in [4, 6, 8, 10, 12, 16]:
        G = grid_cube_graph(L)
        vals.append((L**2) * laplacian_gap(G))
    assert min(vals) > 5.0
    assert max(vals) < 12.0

if __name__ == "__main__":
    test_gap_inverse_square_window()
    print("analytic replacement Laplacian gap test: PASS")
