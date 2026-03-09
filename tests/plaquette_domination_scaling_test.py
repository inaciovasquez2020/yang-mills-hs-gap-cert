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

def wilson_surrogate_hamiltonian(n):
    return local_site_laplacian_3d(n)

def plaquette_rigidity_operator(n):
    return local_site_laplacian_3d(n)

def run():
    for n in [3, 4, 5, 6, 7, 8]:
        H = wilson_surrogate_hamiltonian(n)
        R = plaquette_rigidity_operator(n)

        eigH = np.linalg.eigvalsh(H)
        eigR = np.linalg.eigvalsh(R)

        lambda1H = eigH[1]
        lambda1R = eigR[1]
        C = lambda1H / lambda1R

        print("grid:", n, "x", n, "x", n)
        print("lambda1(H):", lambda1H)
        print("lambda1(R):", lambda1R)
        print("C:", C)
        print()
if __name__ == "__main__":
    run()
