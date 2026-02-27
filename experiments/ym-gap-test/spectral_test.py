import numpy as np
from scipy.sparse import diags
from scipy.sparse.linalg import eigsh

print("Testing discrete Laplacian spectrum")

def laplacian(n):
    # Fixed: added * operator between 2 and np.ones, and -1 and np.ones
    main = 2.0 * np.ones(n)
    off = -1.0 * np.ones(n-1)
    return diags([main, off, off], [0, -1, 1], dtype=float)

for L in [16, 32, 64, 128, 256]:
    A = laplacian(L)
    try:
        vals, _ = eigsh(A, k=1, which='SM')
        print(f"L = {L:4d}, min eigenvalue = {float(vals[0]):.10f}")
    except Exception as e:
        print(f"L = {L:4d}, error: {e}")
