import math
import numpy as np

def cycle_laplacian(n):
    A = np.zeros((n, n))
    for i in range(n):
        A[i, i] = 2
        A[i, (i - 1) % n] = -1
        A[i, (i + 1) % n] = -1
    return A

for n in [8, 16, 32, 64]:
    vals = np.linalg.eigvalsh(cycle_laplacian(n))
    numeric_gap = np.sort(vals)[1]
    analytic_gap = 2 - 2 * math.cos(2 * math.pi / n)
    lower_bound = 4 * math.pi**2 / n**2
    print(n, numeric_gap, analytic_gap, lower_bound, abs(numeric_gap - analytic_gap))
