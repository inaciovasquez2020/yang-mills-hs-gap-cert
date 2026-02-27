import numpy as np
import pytest
from ym.frx.transfer_matrix import lazy_uniform_kernel, dobrushin_tv_contraction

def test_frx_dobrushin_rate_matches_lazy_uniform():
    rng = np.random.default_rng(0)
    for m in [4, 8, 16]:
        for alpha in [0.1, 0.2, 0.35, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            rho = dobrushin_tv_contraction(P)
            # For lazy uniform kernel, contraction rate should be (1-alpha)
            # This is the Dobrushin coefficient ρ = max_{i,j} TV(P_i, P_j)
            expected = 1.0 - alpha
            print(f"m={m}, alpha={alpha}: rho={rho:.6f}, expected={expected:.6f}")
            # Allow small numerical error
            assert abs(rho - expected) < 1e-10, f"rho={rho} != {expected}"

def test_frx_kernel_mixing_time():
    rng = np.random.default_rng(0)
    for m in [8, 16]:
        for alpha in [0.2, 0.5]:
            P = lazy_uniform_kernel(m, alpha)
            rho = dobrushin_tv_contraction(P)
            # Mixing time should be ~ log(2)/log(1/rho)
            mixing_est = np.log(2) / np.log(1/rho)
            print(f"m={m}, alpha={alpha}: mixing time ≈ {mixing_est:.2f}")
            assert mixing_est > 0
            assert mixing_est < 100  # Sanity check
