import numpy as np
from numpy.linalg import eigvalsh
from su2_patch_numeric import su2_identity, random_su2, knn_weights, laplacian_normalized, potential_matrix

def proj_zero_mode(z):
    z = z.reshape(-1,1)
    denom = float((z.T @ z)[0,0])
    return (z @ z.T) / denom

def orth_basis_from_P(P):
    vals, vecs = np.linalg.eigh(P)
    idx = np.argsort(vals)
    vecs = vecs[:, idx]
    n = P.shape[0]
    return vecs[:, :n-1]

def gap_of_sym(A, tol=1e-12):
    w = np.sort(eigvalsh(0.5*(A+A.T)))
    w = w[w > tol]
    return float(w[0]) if w.size else 0.0

def min_C1_for_C2(Aform, Bform, P0, C2, tol=1e-12):
    n = Aform.shape[0]
    Q = orth_basis_from_P(P0)
    A = Q.T @ (np.eye(n) - C2*Aform) @ Q
    B = Q.T @ Bform @ Q
    A = 0.5*(A+A.T)
    B = 0.5*(B+B.T)
    if gap_of_sym(B, tol=tol) <= 0.0:
        return np.inf
    M = np.linalg.solve(B, A)
    M = 0.5*(M+M.T)
    lam = float(np.max(eigvalsh(M)))
    return float(max(lam, 0.0))

def build_forms(n=400, k=12, seed=0):
    U = np.vstack([su2_identity(), random_su2(n-1, seed=seed)])
    W = knn_weights(U, k=k)
    d = np.sum(W, axis=1)
    Dsqrt = np.diag(np.sqrt(np.maximum(d, 1e-12)))
    Lnorm = laplacian_normalized(W)
    V = potential_matrix(U)

    Bform = Dsqrt @ Lnorm @ Dsqrt
    Aform = Dsqrt @ V @ Dsqrt

    z0 = np.sqrt(np.maximum(d, 1e-12))
    P0 = proj_zero_mode(z0)

    return Aform, Bform, P0

def grid_search(n=400, k=12, seed=0, C2max=200.0, m=2001):
    Aform, Bform, P0 = build_forms(n=n, k=k, seed=seed)
    bestC1 = np.inf
    bestC2 = None
    for C2 in np.linspace(0.0, C2max, m):
        C1 = min_C1_for_C2(Aform, Bform, P0, float(C2))
        if C1 < bestC1:
            bestC1 = C1
            bestC2 = float(C2)
    return bestC1, bestC2

if __name__ == "__main__":
    C1, C2 = grid_search(n=400, k=12, seed=0, C2max=200.0, m=2001)
    print("best_C2_grid:", C2)
    print("best_C1_at_C2:", C1)
