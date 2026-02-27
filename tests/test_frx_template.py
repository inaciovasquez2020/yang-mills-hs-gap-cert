import numpy as np
from ym.frx import lazy_uniform_kernel, dobrushin_tv_contraction, transfer_matrix_contraction_rate


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

def test_frx_contraction_matches_dobrushin():
    for m in [4, 8]:
        for alpha in [0.1, 0.3]:
            P = lazy_uniform_kernel(m, alpha)
            rho = dobrushin_tv_contraction(P)
            rate = transfer_matrix_contraction_rate(P)
            assert abs(rho - rate) < 1e-12

def test_frx_monotone_in_alpha():
    m = 8
    alphas = [0.1, 0.2, 0.4]
    rhos = []
    for alpha in alphas:
        P = lazy_uniform_kernel(m, alpha)
        rhos.append(dobrushin_tv_contraction(P))
    assert rhos[0] < rhos[1] < rhos[2]
