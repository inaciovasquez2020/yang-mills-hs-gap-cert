import sys
import os
import numpy as np
from numpy.linalg import eigvalsh

# Add the current directory to path so we can find plaquette4
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def global_test(num_patches=8, n=200, k=24):
    """Aggregate multiple patches and compute global C1 estimate"""
    A_total = None
    B_total = None
    
    print(f"Building {num_patches} patches with n={n}, k={k}")
    print("-" * 50)
    
    for seed in range(num_patches):
        print(f"  Patch {seed+1}/{num_patches}...")
        A, B, z = build_plaquette_patch(n=n, k=k, seed=seed)
        
        if A_total is None:
            A_total = A.copy()
            B_total = B.copy()
        else:
            A_total += A
            B_total += B
    
    print("\nSolving generalized eigenvalue problem...")
    
    # Normalize matrices to prevent numerical issues
    scale = np.max(np.abs(A_total)) + np.max(np.abs(B_total))
    if scale > 0:
        A_total = A_total / scale
        B_total = B_total / scale
    
    # Regularize B
    eigB = eigvalsh(B_total)
    min_eigB = np.min(eigB)
    print(f"  B matrix: min eigenvalue = {min_eigB:.6e}")
    
    # Add regularization
    reg = max(1e-8, -min_eigB + 1e-8)
    B_reg = B_total + reg * np.eye(B_total.shape[0])
    
    # Solve generalized eigenvalue problem
    try:
        from scipy.linalg import eigh
        w = eigh(A_total, B_reg, eigvals_only=True)
    except ImportError:
        # Fallback to Cholesky
        L = np.linalg.cholesky(B_reg)
        L_inv = np.linalg.inv(L)
        M = L_inv @ A_total @ L_inv.T
        M = 0.5 * (M + M.T)
        w = eigvalsh(M)
    
    # Filter out numerical noise
    w = w[w > 1e-10]
    if len(w) == 0:
        C1 = 0.0
    else:
        C1 = float(np.min(w))  # Smallest positive eigenvalue is the gap
    
    print(f"\nGlobal smallest positive eigenvalue (gap candidate) = {C1:.6e}")
    print(f"Eigenvalue range: [{np.min(w):.6e}, {np.max(w):.6e}]")
    
    return C1

if __name__ == "__main__":
    print("=" * 60)
    print("SMALL LATTICE GAP TEST")
    print("=" * 60)
    
    configs = [
        (2, 50, 8),
        (4, 100, 16),
        (6, 150, 24),
        (8, 200, 32),
        (10, 250, 40),
        (12, 300, 48),
    ]
    
    for num_patches, n, k in configs:
        print("\n" + "=" * 60)
        gap = global_test(num_patches=num_patches, n=n, k=k)
        print(f"Config: patches={num_patches}, n={n}, k={k} → gap = {gap:.6e}")
