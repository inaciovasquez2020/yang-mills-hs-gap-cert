import numpy as np
from mass_gap_comparison import laplacian_matrix

def hessian_with_mass(L, m2):
    Δ = laplacian_matrix(L)
    return Δ + m2 * np.eye(L)

def test_uniform_mass_floor():
    m2 = 8.0
    for L in [4, 6, 8, 16, 32, 64, 128]:
        H = hessian_with_mass(L, m2)
        eigvals = np.linalg.eigvalsh(H)
        lam_min = np.min(eigvals)
        assert lam_min >= m2 - 1e-10
