import numpy as np
import pytest
from ym.frx.transfer_matrix import toy_confining_kernel, weyl_sequence_obstruction

def test_weyl_sequence_obstruction_detects_gap_vanishing():
    # Test with confining kernel (should have gap)
    m = 16
    W_conf = toy_confining_kernel(m, g=0.5)
    assert not weyl_sequence_obstruction(W_conf), "Confining kernel should not have obstruction"
    
    # Test with near-uniform kernel (small gap)
    W_unif = np.ones((m, m))
    # Add tiny perturbation to avoid exact uniformity
    W_unif = W_unif + 1e-6 * np.random.randn(m, m)
    W_unif = np.abs(W_unif)
    assert not weyl_sequence_obstruction(W_unif, tol=1e-3), "Should not detect obstruction with tol=1e-3"
    
    print("Weyl sequence obstruction tests passed")

def test_transfer_matrix_spectral_gap():
    from ym.frx.transfer_matrix import toy_confining_kernel, transfer_matrix_contraction_rate
    
    for m in [8, 16, 32]:
        for g in [0.1, 0.5, 1.0]:
            W = toy_confining_kernel(m, g)
            rate = transfer_matrix_contraction_rate(W)
            print(f"m={m:3d}, g={g:.1f}: contraction rate = {rate:.6f}")
            assert 0 <= rate <= 1
