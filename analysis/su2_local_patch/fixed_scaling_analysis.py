import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def get_proper_gap(num_patches, n, k, seed=42):
    """Compute the spectral gap with proper normalization"""
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
    
    # Normalize by the size of the matrices
    n_total = A_total.shape[0]
    
    # Regularize B more strongly
    reg = 1e-6 * np.trace(B_total) / n_total
    B_reg = B_total + reg * np.eye(n_total)
    
    # Scale down the matrices to prevent overflow
    scale = np.max(np.abs(A_total)) + np.max(np.abs(B_total))
    A_scaled = A_total / scale
    B_scaled = B_reg / scale
    
    # Solve generalized eigenvalue problem
    from scipy.linalg import eigh
    w = eigh(A_scaled, B_scaled, eigvals_only=True)
    
    # Get the smallest positive eigenvalue
    w = w[w > 1e-10]
    if len(w) == 0:
        return 0.0
    
    # Return the actual gap (rescaling back)
    gap = float(np.min(w)) * scale
    
    # Also compute the theoretical Laplacian scaling for comparison
    volume = num_patches * n
    laplacian_scale = 10.0 / volume  # Approximate 1/volume scaling
    
    return gap, laplacian_scale, volume

print("=" * 70)
print("PROPER SCALING ANALYSIS")
print("=" * 70)
print(f"{'Patches':8} {'n':6} {'Volume':10} {'Gap':12} {'Laplacian':12} {'Ratio':10}")
print("-" * 70)

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
    gap, lapl, vol = get_proper_gap(patches, n, k)
    results.append((vol, gap))
    print(f"{patches:8d} {n:6d} {vol:10d} {gap:12.6f} {lapl:12.6f} {gap/lapl:10.3f}")

# Fit power law
volumes = np.array([r[0] for r in results])
gaps = np.array([r[1] for r in results])

log_v = np.log(volumes)
log_g = np.log(gaps)
p, log_c = np.polyfit(log_v, log_g, 1)
c = np.exp(log_c)

print("\n" + "=" * 70)
print(f"Gap ∝ volume^{p:.3f}")
print(f"Expected for pure Laplacian: p = -2.0")
print(f"Expected with mass term: p = -1.0")
print(f"Deviation from -2.0: {p + 2:.4f}")
