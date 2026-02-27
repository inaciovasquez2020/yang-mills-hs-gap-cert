import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def analyze_single_patch_scaling():
    """Analyze scaling by increasing n in a single patch"""
    print("=" * 70)
    print("SINGLE PATCH SCALING ANALYSIS")
    print("=" * 70)
    print(f"{'n':8} {'k':6} {'Volume':10} {'Gap':12} {'Gap×√n':12} {'Theory 1/√n':12}")
    print("-" * 70)
    
    results = []
    # Test increasing n with fixed k ≈ n/6 to maintain similar connectivity
    for n in [50, 100, 150, 200, 250, 300, 350, 400]:
        k = max(8, n // 6)
        A, B, z = build_plaquette_patch(n=n, k=k, seed=42)
        
        # Extract normalized Laplacian from B
        deg = np.sum(B != 0, axis=1)
        deg = np.maximum(deg, 1e-10)
        D_inv_sqrt = np.diag(1.0/np.sqrt(deg))
        Lnorm = D_inv_sqrt @ B @ D_inv_sqrt
        
        # Get eigenvalues
        eigvals = np.linalg.eigvalsh(Lnorm)
        sorted_eigs = np.sort(eigvals)
        
        # Find gap (smallest non-zero eigenvalue)
        zero_tol = 1e-8
        non_zero = sorted_eigs[sorted_eigs > zero_tol]
        gap = float(non_zero[0]) if len(non_zero) > 0 else 0.0
        
        # Theoretical continuum scaling: gap ∝ 1/L² ∝ 1/√n (since n ∝ volume ∝ L⁴)
        theory = 1.0 / np.sqrt(n)
        
        results.append((n, gap))
        print(f"{n:8d} {k:6d} {n:10d} {gap:12.6f} {gap*np.sqrt(n):12.6f} {theory:12.6f}")
    
    # Fit power law
    n_vals = np.array([r[0] for r in results])
    gaps = np.array([r[1] for r in results])
    
    log_n = np.log(n_vals)
    log_g = np.log(gaps)
    p, log_c = np.polyfit(log_n, log_g, 1)
    c = np.exp(log_c)
    
    print("\n" + "=" * 70)
    print(f"Gap ∝ n^{p:.3f}")
    print(f"Expected for continuum: p = -0.500 (since n ∝ volume ∝ L⁴, gap ∝ 1/L² ∝ 1/√n)")
    print(f"Deviation from -0.5: {p + 0.5:.4f}")
    print(f"Gap × √n should be constant ≈ {np.mean(gaps * np.sqrt(n_vals)):.4f}")

if __name__ == "__main__":
    analyze_single_patch_scaling()
