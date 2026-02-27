import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from su2_ops import su2_identity, random_su2, su2_mul, su2_inv, trace_real, knn_weights, laplacian_normalized

def build_plaquette_patch(n=200, k=24, seed=0):
    """Build a single plaquette patch"""
    # Generate random SU(2) matrices for links
    U1 = random_su2(n, seed)
    U2 = random_su2(n, seed+1)
    U3 = random_su2(n, seed+2)
    U4 = random_su2(n, seed+3)
    
    # Compute plaquette variable
    Up = su2_mul(su2_mul(su2_mul(U1, U2), su2_inv(U3)), su2_inv(U4))
    
    # Features for graph construction
    X = np.hstack([U1, U2, U3, U4, Up])
    
    # Build graph Laplacian
    W = knn_weights(X, k=k)
    deg = np.sum(W, axis=1)
    Lnorm = laplacian_normalized(W)
    
    # Potential from plaquette
    V = 2.0 - trace_real(Up)
    
    # Build matrices
    Dsqrt = np.diag(np.sqrt(np.maximum(deg, 1e-12)))
    B = Dsqrt @ Lnorm @ Dsqrt
    A = Dsqrt @ np.diag(V) @ Dsqrt
    z0 = np.sqrt(np.maximum(deg, 1e-12))
    
    return A, B, z0
