import numpy as np

def idx(n, i, j, k):
    return (i % n) * n * n + (j % n) * n + (k % n)

def local_laplacian_3d(n):
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

def curvature_stiffness_operator(n, mass):
    N = n * n * n
    return (mass ** 2) * np.eye(N, dtype=float)

def run():
    mass = 0.75

    for n in [3, 4, 5, 6, 7, 8, 9, 10]:
        Delta = local_laplacian_3d(n)
        M = curvature_stiffness_operator(n, mass)
        R = Delta + M

        eigR = np.linalg.eigvalsh(R)
        lambda0 = eigR[0]
        lambda1 = eigR[1]

        print("grid:", n, "x", n, "x", n)
        print("mass:", mass)
        print("lambda0(R):", lambda0)
        print("lambda1(R):", lambda1)
        print("expected floor:", mass ** 2)
        print()

if __name__ == "__main__":
    run()
