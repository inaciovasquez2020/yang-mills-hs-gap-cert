import sys
import os
import numpy as np
from numpy.linalg import eigvalsh
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def global_test_fixed(num_patches=8, n=200, k=24, seed=0):
    """Fixed seed version for consistent scaling analysis"""
    A_total = None
    B_total = None
    
    for i in range(num_patches):
        A, B, z = build_plaquette_patch(n=n, k=k, seed=seed + i*1000)
        
        if A_total is None:
            A_total = A.copy()
            B_total = B.copy()
        else:
            A_total += A
            B_total += B
    
    # Regularize
    scale = np.max(np.abs(A_total)) + np.max(np.abs(B_total))
    if scale > 0:
        A_total = A_total / scale
        B_total = B_total / scale
    
    eigB = eigvalsh(B_total)
    reg = max(1e-8, -np.min(eigB) + 1e-8)
    B_reg = B_total + reg * np.eye(B_total.shape[0])
    
    # Get smallest positive eigenvalue
    try:
        from scipy.linalg import eigh
        w = eigh(A_total, B_reg, eigvals_only=True)
    except:
        L = np.linalg.cholesky(B_reg)
        L_inv = np.linalg.inv(L)
        M = L_inv @ A_total @ L_inv.T
        M = 0.5 * (M + M.T)
        w = eigvalsh(M)
    
    w = w[w > 1e-10]
    return float(np.min(w)) if len(w) > 0 else 0.0

def scaling_analysis():
    print("="*60)
    print("SCALING ANALYSIS WITH FIXED SEED")
    print("="*60)
    
    configs = [
        (2, 50, 8),
        (4, 100, 16),
        (6, 150, 24),
        (8, 200, 32),
        (10, 250, 40),
        (12, 300, 48),
    ]
    
    results = []
    for patches, n, k in configs:
        gap = global_test_fixed(num_patches=patches, n=n, k=k, seed=42)
        volume = patches * n
        results.append((volume, gap))
        print(f"Volume={volume:5d}: gap={gap:.6f}")
    
    # Analyze scaling
    volumes = np.array([r[0] for r in results])
    gaps = np.array([r[1] for r in results])
    
    log_v = np.log(volumes)
    log_g = np.log(gaps)
    p, log_c = np.polyfit(log_v, log_g, 1)
    c = np.exp(log_c)
    
    print("\n" + "="*60)
    print(f"Gap ∝ volume^{p:.3f}")
    print(f"Expected: p = -2.0 for pure Laplacian")
    print(f"Deviation from -2.0: {p + 2:.4f}")

if __name__ == "__main__":
    scaling_analysis()
