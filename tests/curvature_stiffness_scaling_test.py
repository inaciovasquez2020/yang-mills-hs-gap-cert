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
    target = mass ** 2

    for n in [3, 4, 5, 6, 7, 8, 9, 10]:
        Delta = local_laplacian_3d(n)
        R = Delta + target * np.eye(Delta.shape[0], dtype=float)
        eigR = np.linalg.eigvalsh(R)

        print("grid:", n, "x", n, "x", n)
        print("lambda0(R):", eigR[0])
        print("lambda1(R):", eigR[1])
        print("lambda1(R) - mass^2:", eigR[1] - target)
        print()

if __name__ == "__main__":
    run()
