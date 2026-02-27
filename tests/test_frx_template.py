import numpy as np
from ym.frx import lazy_uniform_kernel, dobrushin_tv_contraction


def test_frx_dobrushin_rate_matches_lazy_uniform():
    for m in [4, 8, 16]:
        for alpha in [0.1, 0.2, 0.35, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            rho = dobrushin_tv_contraction(P)

            expected = 0.5 * max(np.sum(np.abs(P[i]-P[j])) for i in range(m) for j in range(m))

            print(f"m={m}, alpha={alpha}: rho={rho:.6f}, expected={expected:.6f}")
            assert abs(rho - expected) < 1e-10


def test_frx_kernel_mixing_time():
    m = 16
    alpha = 0.2
    P = lazy_uniform_kernel(m, alpha)
    rho = dobrushin_tv_contraction(P)
    assert 0.0 <= rho <= 1.0 + 1e-12
