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

def run():
    mass = 0.75
    m2 = mass ** 2

    for n in [3, 4, 5, 6, 7, 8]:
        H = local_laplacian_3d(n) + m2 * np.eye(n * n * n, dtype=float)
        R = local_laplacian_3d(n) + m2 * np.eye(n * n * n, dtype=float)

        eigH = np.linalg.eigvalsh(H)
        eigR = np.linalg.eigvalsh(R)

        C = eigH[1] / eigR[1]

        print("grid:", n, "x", n, "x", n)
        print("lambda1(H):", eigH[1])
        print("lambda1(R):", eigR[1])
        print("C:", C)
        print()

if __name__ == "__main__":
    run()
