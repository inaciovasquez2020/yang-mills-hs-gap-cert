import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def debug_eigenvalues(num_patches=4, n=100, k=16, seed=42):
    print(f"\nDebug: patches={num_patches}, n={n}, k={k}")
    print("-" * 50)
    
    A_total = None
    B_total = None
    
    for i in range(num_patches):
        A, B, z = build_plaquette_patch(n=n, k=k, seed=seed + i*1000)
        print(f"  Patch {i+1}: A shape={A.shape}, B shape={B.shape}")
        
        if A_total is None:
            A_total = A.copy()
            B_total = B.copy()
        else:
            A_total += A
            B_total += B
    
    # Check eigenvalue ranges
    eigA = np.linalg.eigvalsh(A_total)
    eigB = np.linalg.eigvalsh(B_total)
    
    print(f"\n  A matrix: min={np.min(eigA):.3e}, max={np.max(eigA):.3e}")
    print(f"  B matrix: min={np.min(eigB):.3e}, max={np.max(eigB):.3e}")
    
    # Try different ways to get the gap
    scale = np.max(np.abs(A_total)) + np.max(np.abs(B_total))
    A_norm = A_total / scale
    B_norm = B_total / scale
    
    # Regularize
    reg = 1e-8
    B_reg = B_norm + reg * np.eye(B_norm.shape[0])
    
    # Solve generalized eigenvalue problem
    try:
        from scipy.linalg import eigh
        w = eigh(A_norm, B_reg, eigvals_only=True)
        print(f"\n  All eigenvalues (scipy): min={np.min(w):.3e}, max={np.max(w):.3e}")
        print(f"  Smallest positive: {np.min(w[w>1e-10]):.3e}")
    except:
        pass
    
    # Also compute simple eigenvalues of A and B separately
    print(f"\n  A_norm eigenvalues: min={np.min(np.linalg.eigvalsh(A_norm)):.3e}")
    print(f"  B_norm eigenvalues: min={np.min(np.linalg.eigvalsh(B_norm)):.3e}")

if __name__ == "__main__":
    debug_eigenvalues(num_patches=2, n=50, k=8)
    debug_eigenvalues(num_patches=4, n=100, k=16)
