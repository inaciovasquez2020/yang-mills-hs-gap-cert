import math
import numpy as np
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh

def cube_laplacian(L):
    n = L**3
    A = lil_matrix((n, n))

    def idx(x, y, z):
        return x * L * L + y * L + z

    for x in range(L):
        for y in range(L):
            for z in range(L):
                i = idx(x, y, z)
                deg = 0
                for dx, dy, dz in [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]:
                    nx, ny, nz = x + dx, y + dy, z + dz
                    if 0 <= nx < L and 0 <= ny < L and 0 <= nz < L:
                        j = idx(nx, ny, nz)
                        A[i, j] = -1
                        deg += 1
                A[i, i] = deg

    return A.tocsr()

for L in [4, 6, 8, 10, 12]:
    vals = eigsh(cube_laplacian(L), k=2, which="SM", return_eigenvectors=False)
    vals = np.sort(vals)
    numeric_gap = vals[1]
    analytic_gap = 2 - 2 * math.cos(math.pi / (L + 1))
    lower_bound = (math.pi ** 2) / (2 * (L + 1) ** 2)
    print(L, numeric_gap, analytic_gap, lower_bound, abs(numeric_gap - analytic_gap))
