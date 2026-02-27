import numpy as np
from scipy.linalg import eigh

def hessian_A0(L, beta=1.0, mass=8.0):
    """Hessian for A0 field in axial gauge with mass term"""
    n = L
    H = np.zeros((n, n))
    for i in range(n):
        H[i, i] = 2.0 * beta + mass  # Add mass term
        if i > 0:
            H[i, i-1] = -beta
        if i < n-1:
            H[i, i+1] = -beta
    # Periodic boundary
    H[0, n-1] = -beta
    H[n-1, 0] = -beta
    return H

print("Axial Gauge Hessian Spectrum (with mass term m²=8.0)")
print("="*50)
for L in [4, 8, 16, 32, 64, 128]:
    H = hessian_A0(L, mass=8.0)
    eigvals = eigh(H, eigvals_only=True)
    min_eig = np.min(eigvals)
    print(f"L={L:4d}, min eigenvalue = {min_eig:.6f}, asymptotic = {min_eig:.4f} (should approach 8.0)")
