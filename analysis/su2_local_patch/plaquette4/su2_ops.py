import numpy as np
from numpy.linalg import eigvalsh

def su2_identity():
    return np.array([[1.0,0.0,0.0,0.0]])

def random_su2(n, seed=0):
    rng = np.random.default_rng(seed)
    v = rng.normal(size=(n,4))
    v /= np.linalg.norm(v,axis=1)[:,None]
    return v

def su2_mul(A,B):
    a0,a1,a2,a3 = A.T
    b0,b1,b2,b3 = B.T
    c0 = a0*b0 - a1*b1 - a2*b2 - a3*b3
    c1 = a0*b1 + a1*b0 + a2*b3 - a3*b2
    c2 = a0*b2 - a1*b3 + a2*b0 + a3*b1
    c3 = a0*b3 + a1*b2 - a2*b1 + a3*b0
    C = np.vstack([c0,c1,c2,c3]).T
    C /= np.linalg.norm(C,axis=1)[:,None]
    return C

def su2_inv(A):
    B = A.copy()
    B[:,1:] *= -1.0
    return B

def trace_real(A):
    return 2.0*A[:,0]

def knn_weights(X, k=12, sigma=None):
    n = X.shape[0]
    D2 = np.sum((X[:,None,:]-X[None,:,:])**2, axis=2)
    np.fill_diagonal(D2, np.inf)
    nn_idx = np.argpartition(D2, kth=k-1, axis=1)[:, :k]
    nn_d2 = np.take_along_axis(D2, nn_idx, axis=1)
    if sigma is None:
        sigma = np.sqrt(np.median(nn_d2))
        if not np.isfinite(sigma) or sigma <= 0:
            sigma = 1.0
    W = np.zeros((n,n))
    for i in range(n):
        js = nn_idx[i]
        w = np.exp(-nn_d2[i]/(sigma**2))
        W[i, js] = w
    W = np.maximum(W, W.T)
    return W

def laplacian_normalized(W, tol=1e-12):
    deg = np.sum(W, axis=1)
    invsqrt = 1.0/np.sqrt(np.maximum(deg, tol))
    Dm = np.diag(invsqrt)
    I = np.eye(W.shape[0])
    return I - Dm @ W @ Dm

def gap_of(H, tol=1e-10):
    w = np.sort(eigvalsh(0.5*(H+H.T)))
    w = w[w > tol]
    return float(w[0]) if w.size else 0.0
