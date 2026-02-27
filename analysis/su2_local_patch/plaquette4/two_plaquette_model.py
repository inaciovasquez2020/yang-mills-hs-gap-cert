import numpy as np

def random_su2(n, seed=0):
    """Generate n random SU(2) matrices"""
    rng = np.random.default_rng(seed)
    # Generate random unit quaternions
    theta = rng.random(n) * 2 * np.pi
    phi = np.arccos(2 * rng.random(n) - 1)
    
    a = np.cos(theta/2)
    b = np.sin(theta/2) * np.cos(phi)
    c = np.sin(theta/2) * np.sin(phi) * np.cos(rng.random(n) * 2 * np.pi)
    d = np.sin(theta/2) * np.sin(phi) * np.sin(rng.random(n) * 2 * np.pi)
    
    return np.column_stack([a, b, c, d])

def su2_mul(u, v):
    """Multiply two SU(2) matrices (quaternions)"""
    a1, b1, c1, d1 = u.T
    a2, b2, c2, d2 = v.T
    return np.column_stack([
        a1*a2 - b1*b2 - c1*c2 - d1*d2,
        a1*b2 + b1*a2 + c1*d2 - d1*c2,
        a1*c2 - b1*d2 + c1*a2 + d1*b2,
        a1*d2 + b1*c2 - c1*b2 + d1*a2
    ])

def su2_inv(u):
    """Inverse of SU(2) matrix (quaternion conjugate)"""
    a, b, c, d = u.T
    return np.column_stack([a, -b, -c, -d])

def trace_real(u):
    """Trace of SU(2) matrix = 2*a"""
    return 2.0 * u[:, 0]

def sample_links(n, seed=0):
    """Sample 7 SU(2) link variables per configuration"""
    rng = np.random.default_rng(seed)
    links = []
    for i in range(7):
        links.append(random_su2(n, seed + i*1000))
    return np.array(links)  # Shape (7, n, 4)

def knn_weights(X, k=24, sigma=1.0):
    """Compute k-NN weights using Gaussian kernel"""
    n = X.shape[0]
    
    # Compute pairwise distances
    D2 = np.zeros((n, n))
    for i in range(n):
        for j in range(i+1, n):
            # Euclidean distance in quaternion space
            d2 = np.sum((X[i] - X[j])**2)
            D2[i, j] = d2
            D2[j, i] = d2
    
    # Find k nearest neighbors
    W = np.zeros((n, n))
    for i in range(n):
        # Get distances to all other points
        distances = D2[i]
        # Set self-distance to infinity
        distances[i] = np.inf
        # Get k smallest distances
        idx = np.argpartition(distances, k)[:k]
        # Set weights
        W[i, idx] = np.exp(-distances[idx] / (2 * sigma**2))
    
    # Symmetrize
    W = (W + W.T) / 2
    return W

def laplacian_normalized(W):
    """Compute normalized Laplacian L = I - D^{-1/2} W D^{-1/2}"""
    deg = np.sum(W, axis=1)
    deg_inv_sqrt = np.where(deg > 1e-10, 1.0/np.sqrt(deg), 0.0)
    D_inv_sqrt = np.diag(deg_inv_sqrt)
    L_norm = np.eye(W.shape[0]) - D_inv_sqrt @ W @ D_inv_sqrt
    return L_norm

def holonomy_p1(U):
    """Plaquette 1 holonomy: U1 U2 U3† U4†"""
    return su2_mul(su2_mul(su2_mul(U[0], U[1]), su2_inv(U[2])), su2_inv(U[3]))

def holonomy_p2(U):
    """Plaquette 2 holonomy: U4 U5 U6† U7†"""
    return su2_mul(su2_mul(su2_mul(U[3], U[4]), su2_inv(U[5])), su2_inv(U[6]))

def build_two_patch(n=700, k=24, seed=0):
    """Build two-patch configuration with proper SU(2) structure"""
    U = sample_links(n, seed=seed)
    Up1 = holonomy_p1(U)
    Up2 = holonomy_p2(U)
    
    # Combine features
    X = np.hstack([Up1, Up2])
    
    # Build graph Laplacian
    W = knn_weights(X, k=k)
    deg = np.sum(W, axis=1)
    Lnorm = laplacian_normalized(W)
    
    # Potential energy from plaquettes
    Vp1 = 2.0 - trace_real(Up1)
    Vp2 = 2.0 - trace_real(Up2)
    V = Vp1 + Vp2
    
    # Weighted matrices for generalized eigenvalue problem
    Dsqrt = np.diag(np.sqrt(np.maximum(deg, 1e-12)))
    Bform = Dsqrt @ Lnorm @ Dsqrt
    Aform = Dsqrt @ np.diag(V) @ Dsqrt
    
    # Initial vector
    z0 = np.sqrt(np.maximum(deg, 1e-12))
    
    return Aform, Bform, z0
