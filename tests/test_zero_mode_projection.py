import numpy as np
from mass_gap_comparison import laplacian_matrix

def projection_mean_zero(L):
    N = L
    ones = np.ones((N, 1))
    return np.eye(N) - (1.0/N) * (ones @ ones.T)

def test_zero_mode_projection():
    m2 = 8.0
    for L in [4, 8, 16, 32, 64]:
        Δ = laplacian_matrix(L)
        P = projection_mean_zero(L)

        Δ_proj = P @ Δ @ P
        eig_proj = np.linalg.eigvalsh(Δ_proj)

        # Smallest eigenvalue should be ~0 only once (numerical noise allowed)
        zero_count = np.sum(np.abs(eig_proj) < 1e-8)
        assert zero_count == 1, f"L={L}: Expected 1 zero mode, found {zero_count}"
        print(f"L={L:3d}: Zero mode count = {zero_count} ✓")

        H_proj = P @ (Δ + m2 * np.eye(L)) @ P
        eig_H_proj = np.linalg.eigvalsh(H_proj)

        # Strict positivity after projection
        positive_eigs = eig_H_proj[eig_H_proj > 1e-8]
        min_eig = np.min(positive_eigs)
        print(f"L={L:3d}: min positive eigenvalue = {min_eig:.6f} (≥ {m2})")
        assert min_eig >= m2 - 1e-10, f"L={L}: min eigenvalue {min_eig} < {m2}"

if __name__ == "__main__":
    test_zero_mode_projection()
