import numpy as np
import pytest
from ym.frx import (
    lazy_uniform_kernel,
    toy_confining_kernel,
    transfer_matrix_contraction_rate,
    weyl_sequence_obstruction
)

def test_lazy_uniform_kernel_contraction():
    for m in [4, 8, 16]:
        for alpha in [0.1, 0.3, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            rate = transfer_matrix_contraction_rate(P)
            # For lazy uniform kernel, contraction rate should be (1-alpha)
            expected = 1.0 - alpha
            print(f"m={m}, alpha={alpha}: rate={rate:.6f}, expected={expected:.6f}")
            assert abs(rate - expected) < 1e-10

def test_confining_kernel_contracts():
    for m in [8, 16, 32]:
        for g in [0.2, 0.5, 1.0]:
            W = toy_confining_kernel(m, g)
            # Confining kernels should have spectral gap (no obstruction)
            assert not weyl_sequence_obstruction(W, tol=1e-6)
            
            rate = transfer_matrix_contraction_rate(W)
            print(f"m={m}, g={g}: contraction rate={rate:.6f}")
            # Should be strictly contracting
            assert rate < 1.0
            
            # For strong confinement, rate should be small
            if g >= 1.0 and m <= 16:
                assert rate < 0.99

def test_uniform_kernel_no_gap():
    m = 8
    W_unif = np.ones((m, m))
    # Uniform kernel should have contraction rate = 0 (in our implementation)
    rate = transfer_matrix_contraction_rate(W_unif)
    assert abs(rate - 0.0) < 1e-12
    # And should have spectral gap 0 (obstruction)
    assert weyl_sequence_obstruction(W_unif, tol=1e-6)
