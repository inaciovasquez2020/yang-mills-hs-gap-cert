import numpy as np

def lambda1_periodic_3d_laplacian(n):
    return 6.0 - 2.0 * (
        np.cos(2.0 * np.pi / n) +
        np.cos(0.0) +
        np.cos(0.0)
    )

def run():
    for n in [6, 7, 8, 9, 10]:
        lam = lambda1_periodic_3d_laplacian(n)
        scaled = lam * (n ** 2)
        print("grid:", n, "x", n, "x", n)
        print("lambda1:", lam)
        print("n^2 * lambda1:", scaled)
        print()

if __name__ == "__main__":
    run()
