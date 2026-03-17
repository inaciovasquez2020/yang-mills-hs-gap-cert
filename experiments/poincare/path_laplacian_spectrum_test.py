import numpy as np
from scipy.sparse import lil_matrix
from scipy.sparse.linalg import eigsh
import math

def path_laplacian(L):
    A = lil_matrix((L,L))
    for i in range(L):
        deg = 0
        for j in [i-1,i+1]:
            if 0 <= j < L:
                A[i,j] = -1
                deg += 1
        A[i,i] = deg
    return A.tocsr()

for L in [4,6,8,10,12]:
    vals = eigsh(path_laplacian(L), k=2, which="SM", return_eigenvectors=False)
    vals = np.sort(vals)
    numeric_gap = vals[1]
    analytic_gap = 2 - 2*math.cos(math.pi/(L+1))
    print(L, numeric_gap, analytic_gap, abs(numeric_gap-analytic_gap))
