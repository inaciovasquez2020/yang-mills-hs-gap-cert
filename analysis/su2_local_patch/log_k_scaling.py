import numpy as np
import sys
import os
import math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def analyze_log_k_scaling():
    """Analyze scaling with k proportional to log(n)"""
    print("=" * 70)
    print("KNN SCALING WITH K ∝ LOG(N)")
    print("=" * 70)
    print(f"{'n':8} {'k':6} {'Volume':10} {'Gap':12} {'Gap×log(n)':15} {'Gap×n^(1/4)':15}")
    print("-" * 70)
    
    results = []
    
    for n in [50, 100, 200, 400, 800]:
        # k proportional to log(n)
        k = max(8, int(4 * math.log(n)))
        
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
        
        results.append((n, gap, k))
        
        # Compute scaling factors
        log_n = math.log(n)
        n_quarter = n ** 0.25
        
        gap_log = gap * log_n
        gap_quarter = gap * n_quarter
        
        print(f"{n:8d} {k:6d} {n:10d} {gap:12.6f} {gap_log:15.6f} {gap_quarter:15.6f}")
    
    # Fit power law
    n_vals = np.array([r[0] for r in results])
    gaps = np.array([r[1] for r in results])
    
    log_n = np.log(n_vals)
    log_g = np.log(gaps)
    p, log_c = np.polyfit(log_n, log_g, 1)
    c = np.exp(log_c)
    
    print("\n" + "=" * 70)
    print(f"Gap ∝ n^{p:.3f}")
    print(f"Expected for continuum: p = -0.500 (1/√n)")
    print(f"Expected for random geometric graphs: p ≈ -0.5 to -0.3")
    print(f"Your exponent: {p:.3f}")
    print(f"Interpretation: {'Stronger than expected' if p > -0.3 else 'Weaker than expected'}")

if __name__ == "__main__":
    analyze_log_k_scaling()
