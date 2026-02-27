import numpy as np
from mass_gap_comparison import laplacian_matrix

def test_operator_shift_identity():
m2 = 8.0
for L in [4, 8, 16, 32, 64]:
Δ = laplacian_matrix(L)
H = Δ + m2 * np.eye(L)

    eig_Δ = np.linalg.eigvalsh(Δ)
    assert np.min(eig_Δ) >= -1e-12

    eig_H = np.linalg.eigvalsh(H)
    eig_expected = eig_Δ + m2
    assert np.allclose(eig_H, eig_expected)
