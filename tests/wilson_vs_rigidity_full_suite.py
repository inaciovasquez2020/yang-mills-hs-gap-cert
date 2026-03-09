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

def lambda1_periodic_3d_laplacian(n):
    return 6.0 - 2.0 * (
        np.cos(2.0 * np.pi / n) +
        np.cos(0.0) +
        np.cos(0.0)
    )

def run():
    print("section: exact finite-matrix comparison")
    print()

    for n in [3, 4, 5, 6]:
        H = local_site_laplacian_3d(n)
        R = local_site_laplacian_3d(n)

        eigH = np.linalg.eigvalsh(H)
        eigR = np.linalg.eigvalsh(R)

        lambda0H = eigH[0]
        lambda1H = eigH[1]
        lambda0R = eigR[0]
        lambda1R = eigR[1]
        C = lambda1H / lambda1R

        print("grid:", n, "x", n, "x", n)
        print("lambda0(H):", lambda0H)
        print("lambda1(H):", lambda1H)
        print("lambda0(R):", lambda0R)
        print("lambda1(R):", lambda1R)
        print("C:", C)
        print()

    print("section: asymptotic n^{-2} scaling")
    print()

    for n in [6, 7, 8, 9, 10]:
        lam = lambda1_periodic_3d_laplacian(n)
        print("grid:", n, "x", n, "x", n)
        print("lambda1:", lam)
        print("n^2 * lambda1:", lam * (n ** 2))
        print()

if __name__ == "__main__":
    run()
