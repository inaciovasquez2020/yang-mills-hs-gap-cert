import numpy as np

def cycle_laplacian(n):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, i] = 2
        A[i, (i - 1) % n] = -1
        A[i, (i + 1) % n] = -1
    return A

for n in [8, 16, 32, 64]:
    L = cycle_laplacian(n)
    vals = np.linalg.eigvalsh(L)
    gap = np.sort(vals)[1]
    print(n, gap, n * n * gap)
