import numpy as np

def idx(n, i, j, k):
    return (i % n) * n * n + (j % n) * n + (k % n)

def local_site_laplacian_3d(n):
    N = n * n * n
    L = np.zeros((N, N), dtype=float)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                p = idx(n, i, j, k)
                for di, dj, dk in [
                    (-1, 0, 0), (1, 0, 0),
                    (0, -1, 0), (0, 1, 0),
                    (0, 0, -1), (0, 0, 1),
                ]:
                    q = idx(n, i + di, j + dj, k + dk)
                    L[p, p] += 1.0
                    L[p, q] -= 1.0
    return L

def plaquette_rigidity_operator(n):
    return local_site_laplacian_3d(n)

def run():
    for n in [3, 4, 5]:
        R = plaquette_rigidity_operator(n)
        eig = np.linalg.eigvalsh(R)
        print("plaquette rigidity grid:", n, "x", n, "x", n)
        print("lambda0(R):", eig[0])
        print("lambda1(R):", eig[1])
        print()

if __name__ == "__main__":
    run()
