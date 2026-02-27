import numpy as np
import pytest
from ym.frx import (
    lazy_uniform_kernel, 
    toy_confining_kernel,
    transfer_matrix_contraction_rate,
    weyl_sequence_obstruction
)

def test_lazy_uniform_kernel_spectral_gap():
    for m in [4, 8, 16]:
        for alpha in [0.1, 0.3, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            rate = transfer_matrix_contraction_rate(P)
            expected = 1.0 - alpha
            print(f"m={m}, alpha={alpha}: rate={rate:.6f}, expected={expected:.6f}")
            assert abs(rate - expected) < 1e-10

def test_confining_kernel_has_gap():
    for m in [8, 16, 32]:
        for g in [0.2, 0.5, 1.0]:
            W = toy_confining_kernel(m, g)
            assert not weyl_sequence_obstruction(W, tol=1e-6)
            rate = transfer_matrix_contraction_rate(W)
            print(f"m={m}, g={g}: contraction rate={rate:.6f}")
            assert rate < 0.99  # Should have some contraction

def test_uniform_kernel_obstruction():
    m = 8
    W_unif = np.ones((m, m))
    # Uniform kernel should have no spectral gap (second eigenvalue = 0)
    assert weyl_sequence_obstruction(W_unif, tol=1e-6)
