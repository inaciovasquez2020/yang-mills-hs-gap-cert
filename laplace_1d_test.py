import numpy as np

def laplace_1d_eigs(L):
    k = np.arange(L)
    return 2 - 2 * np.cos(2 * np.pi * k / L)

print("1D Periodic Laplacian Spectrum")
print("="*40)
for L in [4, 6, 8, 10, 16, 32, 64]:
    eigs = laplace_1d_eigs(L)
    pos = eigs[eigs > 1e-12]
    print(f"L={L:3d}, first positive eigenvalue = {pos.min():.8f}, scaled = {pos.min() * L * L:.4f}")
