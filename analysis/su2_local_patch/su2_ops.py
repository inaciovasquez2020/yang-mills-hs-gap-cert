import numpy as np

def su2_identity():
    """Return identity in quaternion representation"""
    return np.array([1.0, 0.0, 0.0, 0.0])

def random_su2(n, seed=0):
    """Generate n random SU(2) matrices in quaternion representation"""
    rng = np.random.default_rng(seed)
    
    # Generate random unit quaternions uniformly on S^3
    # Method: Marsaglia (1972) - efficient and uniform
    x1 = rng.normal(size=n)
    x2 = rng.normal(size=n)
    x3 = rng.normal(size=n)
    x4 = rng.normal(size=n)
    
    norm = np.sqrt(x1**2 + x2**2 + x3**2 + x4**2)
    return np.column_stack([x1/norm, x2/norm, x3/norm, x4/norm])

def su2_mul(u, v):
    """Multiply two SU(2) matrices (quaternions)"""
    if u.ndim == 1:
        u = u.reshape(1, -1)
    if v.ndim == 1:
        v = v.reshape(1, -1)
    
    a1, b1, c1, d1 = u[:, 0], u[:, 1], u[:, 2], u[:, 3]
    a2, b2, c2, d2 = v[:, 0], v[:, 1], v[:, 2], v[:, 3]
    
    return np.column_stack([
        a1*a2 - b1*b2 - c1*c2 - d1*d2,
        a1*b2 + b1*a2 + c1*d2 - d1*c2,
        a1*c2 - b1*d2 + c1*a2 + d1*b2,
        a1*d2 + b1*c2 - c1*b2 + d1*a2
    ])

def su2_inv(u):
    """Inverse of SU(2) matrix (quaternion conjugate)"""
    if u.ndim == 1:
        u = u.reshape(1, -1)
    a, b, c, d = u[:, 0], u[:, 1], u[:, 2], u[:, 3]
    return np.column_stack([a, -b, -c, -d])

def trace_real(u):
    """Trace of SU(2) matrix = 2*a"""
    if u.ndim == 1:
        return 2.0 * u[0]
    return 2.0 * u[:, 0]

def knn_weights(X, k=24, sigma=1.0):
    """Compute k-NN weights using Gaussian kernel"""
    n = X.shape[0]
    
    # Normalize features to prevent numerical issues
    X_mean = np.mean(X, axis=0)
    X_std = np.std(X, axis=0) + 1e-10
    X_norm = (X - X_mean) / X_std
    
    # Compute pairwise distances
    D2 = np.zeros((n, n))
    for i in range(n):
        for j in range(i+1, n):
            d2 = np.sum((X_norm[i] - X_norm[j])**2)
            D2[i, j] = d2
            D2[j, i] = d2
    
    # Find k nearest neighbors
    W = np.zeros((n, n))
    for i in range(n):
        distances = D2[i].copy()
        distances[i] = np.inf
        idx = np.argpartition(distances, k)[:k]
        W[i, idx] = np.exp(-distances[idx] / (2 * sigma**2))
    
    # Symmetrize and normalize
    W = (W + W.T) / 2
    W = W / np.max(W)  # Normalize to [0,1]
    return W

def laplacian_normalized(W):
    """Compute normalized Laplacian L = I - D^{-1/2} W D^{-1/2}"""
    deg = np.sum(W, axis=1)
    deg = np.maximum(deg, 1e-10)
    deg_inv_sqrt = 1.0 / np.sqrt(deg)
    D_inv_sqrt = np.diag(deg_inv_sqrt)
    L_norm = np.eye(W.shape[0]) - D_inv_sqrt @ W @ D_inv_sqrt
    return L_norm
