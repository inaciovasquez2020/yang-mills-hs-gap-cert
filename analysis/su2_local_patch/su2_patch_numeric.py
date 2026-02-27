import numpy as np
from numpy.linalg import eigvalsh

def random_su2(n):
    v = np.random.normal(size=(n,4))
    v /= np.linalg.norm(v,axis=1)[:,None]
    return v

def trace_real(u):
    return 2*u[:,0]

def laplacian_matrix(n,eps=1e-3):
    M = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            if i!=j:
                M[i,j] = np.exp(-np.sum((U[i]-U[j])**2)/(eps**2))
        M[i,i] = -np.sum(M[i])
    return M

def potential_matrix(U):
    V = 2 - trace_real(U)
    return np.diag(V)

def estimate_constants(n=120):
    global U
    U = random_su2(n)
    L = laplacian_matrix(n)
    V = potential_matrix(U)
    H = L + V
    w = eigvalsh(H)
    w = np.sort(w)
    gap = w[1]
    eigL = np.sort(eigvalsh(L))[1]
    eigV = np.min(np.diag(V))
    return gap, eigL, eigV

if __name__ == "__main__":
    gap, eigL, eigV = estimate_constants(150)
    print("Estimated lowest nonzero eigenvalue:", gap)
    print("Electric-only gap estimate:", eigL)
    print("Minimum potential value:", eigV)
