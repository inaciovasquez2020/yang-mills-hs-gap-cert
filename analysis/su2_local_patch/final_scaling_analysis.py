import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def get_normalized_laplacian_gap(num_patches, n, k, seed=42):
    """Build normalized graph Laplacian and compute its spectral gap"""
    L_total = None
    n_total = 0
    
    for i in range(num_patches):
        A, B, z = build_plaquette_patch(n=n, k=k, seed=seed + i*1000)
        
        # B = Dsqrt @ Lnorm @ Dsqrt, so Lnorm = Dsqrt^{-1} @ B @ Dsqrt^{-1}
        deg = np.sum(B != 0, axis=1)
        deg = np.maximum(deg, 1e-10)
        D_inv_sqrt = np.diag(1.0/np.sqrt(deg))
        Lnorm = D_inv_sqrt @ B @ D_inv_sqrt
        
        if L_total is None:
            L_total = Lnorm.copy()
            n_total = Lnorm.shape[0]
        else:
            # This assumes patches are independent - in reality they should connect
            # For now, just track the size
            n_total += Lnorm.shape[0]
    
    # Get eigenvalues of the normalized Laplacian
    eigvals = np.linalg.eigvalsh(L_total)
    sorted_eigs = np.sort(eigvals)
    
    # The spectral gap is the smallest non-zero eigenvalue
    zero_tol = 1e-8
    non_zero = sorted_eigs[sorted_eigs > zero_tol]
    gap = float(non_zero[0]) if len(non_zero) > 0 else 0.0
    
    # For a well-connected graph, the gap should scale as 1/L² in physical units
    # Here L ~ n^(1/4) in 4D, so volume ~ L⁴ ~ n
    volume = num_patches * n
    
    # Expected scaling for continuum: gap ∝ 1/L² ∝ 1/√(volume)
    expected_continuum = 1.0 / np.sqrt(volume)
    
    return gap, volume, expected_continuum

print("=" * 70)
print("NORMALIZED LAPLACIAN SCALING ANALYSIS")
print("=" * 70)
print(f"{'Patches':8} {'n':6} {'Volume':10} {'Gap':12} {'Gap×√V':12} {'Continuum':12}")
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
    gap, vol, cont = get_normalized_laplacian_gap(patches, n, k)
    results.append((vol, gap))
    print(f"{patches:8d} {n:6d} {vol:10d} {gap:12.6f} {gap*np.sqrt(vol):12.6f} {cont:12.6f}")

# Fit power law
volumes = np.array([r[0] for r in results])
gaps = np.array([r[1] for r in results])

log_v = np.log(volumes)
log_g = np.log(gaps)
p, log_c = np.polyfit(log_v, log_g, 1)
c = np.exp(log_c)

print("\n" + "=" * 70)
print(f"Gap ∝ volume^{p:.3f}")
print(f"Expected for continuum Laplacian: p = -0.5 (since gap ∝ 1/L² ∝ 1/√volume)")
print(f"Deviation from -0.5: {p + 0.5:.4f}")
