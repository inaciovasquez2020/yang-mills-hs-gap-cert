import numpy as np
from ym.vortex_mixing.python.nonlinear_wilson_hessian_u1 import (
    wilson_u1_energy, finite_diff_hessian, analytic_hessian_at_vacuum,
    coexact_projector, min_pos_eig
)

def test_u1_wilson_hessian_matches_ctc_at_vacuum():
    L = 4
    beta = 1.0
    nE = 2*L*L
    x0 = np.zeros(nE)
    f = lambda th: wilson_u1_energy(th, L=L, beta=beta)
    H_fd = finite_diff_hessian(f, x0, eps=1e-6)
    H_an = analytic_hessian_at_vacuum(L, beta=beta)
    err = np.max(np.abs(H_fd - H_an))
    assert err < 5e-4

def test_u1_coexact_has_positive_gap_and_scales_like_L_inv2():
    beta = 1.0
    sizes = [4, 6, 8, 10]
    scaled = []
    for L in sizes:
        H = analytic_hessian_at_vacuum(L, beta=beta)
        P = coexact_projector(L)
        Hc = P @ H @ P
        lam = min_pos_eig(Hc)
        assert lam is not None
        scaled.append(lam * (L**2))
    r = max(scaled) / min(scaled)
    assert r < 2.5
