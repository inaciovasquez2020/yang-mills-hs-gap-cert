import numpy as np
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def analyze_knn_scaling_fixed_k():
    """Analyze scaling with fixed k (k=24) as n increases"""
    print("=" * 70)
    print("KNN SCALING WITH FIXED K = 24")
    print("=" * 70)
    print(f"{'n':8} {'Volume':10} {'Gap':12} {'Gap×n^(1/2)':15} {'Gap×n':12}")
    print("-" * 70)
    
    results = []
    k_fixed = 24
    
    for n in [50, 100, 150, 200, 250, 300, 350, 400]:
        A, B, z = build_plaquette_patch(n=n, k=k_fixed, seed=42)
        
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
        
        results.append((n, gap))
        
        # Compute scaling factors
        sqrt_n = np.sqrt(n)
        gap_sqrt = gap * sqrt_n
        gap_n = gap * n
        
        print(f"{n:8d} {n:10d} {gap:12.6f} {gap_sqrt:15.6f} {gap_n:12.6f}")
    
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
    print(f"Expected for well-connected graph: p ≈ 0.0")
    print(f"Deviation from -0.5: {p + 0.5:.4f}")
    print(f"Deviation from 0.0: {p:.4f}")

if __name__ == "__main__":
    analyze_knn_scaling_fixed_k()
