import networkx as nx
import numpy as np

def laplacian_gap(G):
    L = nx.laplacian_matrix(G).todense()
    w = np.linalg.eigvalsh(L)
    return float(sorted(w)[1])

def test_gap_times_n_squared_stabilizes():
    vals = []
    for n in [6, 8, 10, 12, 14]:
        G = nx.grid_2d_graph(n, n)
        gap = laplacian_gap(G)
        vals.append(gap * (n ** 2))

    assert min(vals) > 5.0
    assert max(vals) < 12.0

if __name__ == "__main__":
    test_gap_times_n_squared_stabilizes()
    print("gap scaling test: PASS")
