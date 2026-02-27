import numpy as np
from math import pi

def build_grad(L):
    n = L*L
    G = np.zeros((2*n, n))
    def idx(x,y): return (x%L) + L*(y%L)
    for y in range(L):
        for x in range(L):
            v = idx(x,y)
            ex = idx(x,y)
            ey = n + idx(x,y)
            G[ex, v] = -1
            G[ex, idx(x+1,y)] = 1
            G[ey, v] = -1
            G[ey, idx(x,y+1)] = 1
    return G

def build_curl(L):
    n = L*L
    C = np.zeros((n, 2*n))
    def idx(x,y): return (x%L) + L*(y%L)
    for y in range(L):
        for x in range(L):
            f = idx(x,y)
            C[f, idx(x,y)] = 1
            C[f, n+idx(x+1,y)] = 1
            C[f, idx(x,y+1)] = -1
            C[f, n+idx(x,y)] = -1
    return C

def orth_proj(A, tol=1e-12):
    U, s, _ = np.linalg.svd(A, full_matrices=False)
    r = np.sum(s > tol*s[0]) if s.size>0 else 0
    if r == 0:
        return np.zeros((A.shape[0],A.shape[0]))
    return U[:,:r] @ U[:,:r].T

def min_pos_eig(M, tol=1e-8):
    w = np.linalg.eigvalsh(0.5*(M+M.T))
    w = w[w>tol]
    return None if w.size==0 else float(np.min(w))

def test_exact_coexact_poincare_matrix_bound():
    for L in [8,12,16]:
        G = build_grad(L)
        C = build_curl(L)
        PG = orth_proj(G)
        Pco = orth_proj(C.T) @ (np.eye(PG.shape[0]) - PG)
        Lap = C.T @ C
        H = Pco @ Lap @ Pco
        lam = min_pos_eig(H)
        assert lam is not None
        assert lam * (L**2) > 30.0
