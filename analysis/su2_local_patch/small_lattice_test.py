import sys
import os
import numpy as np
from numpy.linalg import eigvalsh

# Add parent directory to path so we can import su2_ops
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
    
    # Normalize matrices to prevent numerical explosion
    scale = np.max(np.abs(A_total)) + np.max(np.abs(B_total))
    if scale > 0:
        A_total = A_total / scale
        B_total = B_total / scale
    
    # Regularize B
    eigB = eigvalsh(B_total)
    min_eigB = np.min(eigB)
    print(f"  B matrix: min eigenvalue = {min_eigB:.6e}")
    
    # Add stronger regularization
    reg = max(1e-8, -min_eigB + 1e-8)
    B_reg = B_total + reg * np.eye(B_total.shape[0])
    print(f"  Added regularization: {reg:.6e}")
    
    # Solve generalized eigenvalue problem
    try:
        # Use scipy if available for better stability
        try:
            from scipy.linalg import eigh
            w = eigh(A_total, B_reg, eigvals_only=True)
        except ImportError:
            # Fallback to regular eigvalsh after transformation
            L = np.linalg.cholesky(B_reg)
            L_inv = np.linalg.inv(L)
            M = L_inv @ A_total @ L_inv.T
            M = 0.5 * (M + M.T)
            w = eigvalsh(M)
    except Exception as e:
        print(f"  Error in eigenvalue computation: {e}")
        return np.nan
    
    # Filter out numerical noise
    w = w[w > 1e-10]
    if len(w) == 0:
        C1 = 0.0
    else:
        C1 = float(np.max(w))
    
    print(f"\nGlobal C1 estimate = {C1:.6f}")
    print(f"  eigenvalue range: [{np.min(w):.6e}, {C1:.6f}]")
    
    return C1

if __name__ == "__main__":
    print("=" * 60)
    print("SMALL LATTICE GLOBAL TEST")
    print("=" * 60)
    
    # Test with different configurations
    configs = [
        (2, 50, 8),    # patches, n, k (smaller to start)
        (4, 100, 16),
        (6, 150, 24),
    ]
    
    for num_patches, n, k in configs:
        print("\n" + "=" * 60)
        C1 = global_test(num_patches=num_patches, n=n, k=k)
        print(f"Config: patches={num_patches}, n={n}, k={k} → C1 = {C1:.6f}")
