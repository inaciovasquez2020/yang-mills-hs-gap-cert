import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def get_laplacian_gap(num_patches, n, k, seed=42):
    """Build the graph Laplacian directly and compute its smallest eigenvalue"""
    L_total = None
    
    for i in range(num_patches):
        A, B, z = build_plaquette_patch(n=n, k=k, seed=seed + i*1000)
        
        # Reconstruct the Laplacian from B
        # B = Dsqrt @ Lnorm @ Dsqrt, so Lnorm = Dsqrt^{-1} @ B @ Dsqrt^{-1}
        deg = np.sum(B != 0, axis=1)  # Approximate degree from B
        deg = np.maximum(deg, 1e-10)
        D_inv_sqrt = np.diag(1.0/np.sqrt(deg))
        Lnorm = D_inv_sqrt @ B @ D_inv_sqrt
        
        if L_total is None:
            L_total = Lnorm.copy()
        else:
            L_total += Lnorm
    
    # Get the smallest eigenvalue of the Laplacian
    n_total = L_total.shape[0]
    
    # Regularize a tiny bit
    L_reg = L_total + 1e-10 * np.eye(n_total)
    eigvals = np.linalg.eigvalsh(L_reg)
    
    # Smallest eigenvalue should be near 0 (zero mode)
    # Second smallest is the spectral gap
    sorted_eigs = np.sort(eigvals)
    gap = float(sorted_eigs[1]) if len(sorted_eigs) > 1 else float(sorted_eigs[0])
    
    # Also get the Fiedler value (algebraic connectivity)
    volume = num_patches * n
    
    return gap, volume

print("=" * 70)
print("CORRECT LAPLACIAN SCALING ANALYSIS")
print("=" * 70)
print(f"{'Patches':8} {'n':6} {'Volume':10} {'Gap':12} {'Gap×Volume²':15}")
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
    gap, vol = get_laplacian_gap(patches, n, k)
    results.append((vol, gap))
    print(f"{patches:8d} {n:6d} {vol:10d} {gap:12.6f} {gap*vol*vol:15.3f}")

# Fit power law
volumes = np.array([r[0] for r in results])
gaps = np.array([r[1] for r in results])

log_v = np.log(volumes)
log_g = np.log(gaps)
p, log_c = np.polyfit(log_v, log_g, 1)
c = np.exp(log_c)

print("\n" + "=" * 70)
print(f"Gap ∝ volume^{p:.3f}")
print(f"Expected for graph Laplacian: p ≈ -2.0 (since volume ~ L⁴ in 4D)")
print(f"Check: gap × volume² should be constant ≈ {np.mean(gaps * volumes**2):.3f}")
