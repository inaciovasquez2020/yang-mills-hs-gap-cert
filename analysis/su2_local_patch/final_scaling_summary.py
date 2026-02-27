import numpy as np
import matplotlib.pyplot as plt
import sys
import os
import math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from plaquette4.plaquette_model import build_plaquette_patch

def run_comprehensive_scaling_analysis():
    """Run all scaling tests and produce summary"""
    
    results = {
        'fixed_k': {'n': [], 'gap': [], 'k': 24},
        'log_k': {'n': [], 'gap': [], 'k': []},
        'single_patch': {'n': [], 'gap': []}
    }
    
    print("=" * 80)
    print("COMPREHENSIVE SCALING ANALYSIS FOR YANG-MILLS SPECTRAL GAP")
    print("=" * 80)
    
    # Test 1: Fixed k = 24
    print("\n1. FIXED K = 24")
    print("-" * 50)
    k_fixed = 24
    for n in [50, 100, 150, 200, 250, 300, 350, 400]:
        A, B, z = build_plaquette_patch(n=n, k=k_fixed, seed=42)
        
        deg = np.sum(B != 0, axis=1)
        deg = np.maximum(deg, 1e-10)
        D_inv_sqrt = np.diag(1.0/np.sqrt(deg))
        Lnorm = D_inv_sqrt @ B @ D_inv_sqrt
        
        eigvals = np.linalg.eigvalsh(Lnorm)
        sorted_eigs = np.sort(eigvals)
        non_zero = sorted_eigs[sorted_eigs > 1e-8]
        gap = float(non_zero[0]) if len(non_zero) > 0 else 0.0
        
        results['fixed_k']['n'].append(n)
        results['fixed_k']['gap'].append(gap)
        print(f"  n={n:4d}, k={k_fixed:2d}, gap={gap:.6f}")
    
    # Test 2: k ∝ log(n)
    print("\n2. K ∝ LOG(N)")
    print("-" * 50)
    for n in [50, 100, 200, 400, 800]:
        k = max(8, int(4 * math.log(n)))
        A, B, z = build_plaquette_patch(n=n, k=k, seed=42)
        
        deg = np.sum(B != 0, axis=1)
        deg = np.maximum(deg, 1e-10)
        D_inv_sqrt = np.diag(1.0/np.sqrt(deg))
        Lnorm = D_inv_sqrt @ B @ D_inv_sqrt
        
        eigvals = np.linalg.eigvalsh(Lnorm)
        sorted_eigs = np.sort(eigvals)
        non_zero = sorted_eigs[sorted_eigs > 1e-8]
        gap = float(non_zero[0]) if len(non_zero) > 0 else 0.0
        
        results['log_k']['n'].append(n)
        results['log_k']['gap'].append(gap)
        results['log_k']['k'].append(k)
        print(f"  n={n:4d}, k={k:2d}, gap={gap:.6f}")
    
    # Fit power laws
    print("\n" + "=" * 80)
    print("SCALING EXPONENTS")
    print("=" * 80)
    
    for test_name in ['fixed_k', 'log_k']:
        n = np.array(results[test_name]['n'])
        gap = np.array(results[test_name]['gap'])
        
        log_n = np.log(n)
        log_g = np.log(gap)
        p, log_c = np.polyfit(log_n, log_g, 1)
        c = np.exp(log_c)
        
        print(f"\n{test_name.upper()} : gap ∝ n^{p:.3f}")
        print(f"  Theoretical continuum: p = -0.500")
        print(f"  Your result: p = {p:+.3f}")
        print(f"  Interpretation: {'Gap grows with volume' if p>0 else 'Gap decays with volume'}")
    
    # Create visualization
    plt.figure(figsize=(12, 5))
    
    plt.subplot(1, 2, 1)
    plt.plot(results['fixed_k']['n'], results['fixed_k']['gap'], 'bo-', linewidth=2, markersize=8, label='Fixed k=24')
    plt.plot(results['log_k']['n'], results['log_k']['gap'], 'rs-', linewidth=2, markersize=8, label='k ∝ log(n)')
    plt.xlabel('n (number of points)', fontsize=12)
    plt.ylabel('Spectral Gap', fontsize=12)
    plt.title('Gap vs System Size', fontsize=14)
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.subplot(1, 2, 2)
    plt.loglog(results['fixed_k']['n'], results['fixed_k']['gap'], 'bo-', linewidth=2, markersize=8, label='Fixed k=24')
    plt.loglog(results['log_k']['n'], results['log_k']['gap'], 'rs-', linewidth=2, markersize=8, label='k ∝ log(n)')
    plt.loglog(results['fixed_k']['n'], 0.1/np.sqrt(results['fixed_k']['n']), 'k--', linewidth=2, label='1/√n (continuum)')
    plt.xlabel('n (log scale)', fontsize=12)
    plt.ylabel('Spectral Gap (log scale)', fontsize=12)
    plt.title('Log-Log Plot: Scaling Exponent', fontsize=14)
    plt.legend()
    plt.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('gap_scaling_summary.png', dpi=150)
    print("\n✓ Saved gap_scaling_summary.png")

if __name__ == "__main__":
    run_comprehensive_scaling_analysis()
