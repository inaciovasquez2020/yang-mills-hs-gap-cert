import numpy as np

def grid_laplacian_3d(n):
    N = n * n * n
    L = np.zeros((N, N))

    def idx(i, j, k):
        return (i % n) * n * n + (j % n) * n + (k % n)

    for i in range(n):
        for j in range(n):
            for k in range(n):
                p = idx(i, j, k)
                for di, dj, dk in [
                    (-1, 0, 0), (1, 0, 0),
                    (0, -1, 0), (0, 1, 0),
                    (0, 0, -1), (0, 0, 1),
                ]:
                    q = idx(i + di, j + dj, k + dk)
                    L[p, p] += 1.0
                    L[p, q] -= 1.0
    return L

def run():
    for n in [3, 4, 5]:
        H = grid_laplacian_3d(n)
        R = grid_laplacian_3d(n)

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
