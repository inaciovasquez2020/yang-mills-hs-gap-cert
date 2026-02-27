import numpy as np
from ym.vortex_mixing.python.nonlinear_wilson_hessian_u1 import (
    analytic_hessian_at_vacuum, coexact_projector, min_pos_eig
)

def test_extract_coexact_poincare_constant_lower_bound():
    beta = 1.0
    sizes = [4, 6, 8, 10, 12]
    vals = []
    for L in sizes:
        H = analytic_hessian_at_vacuum(L, beta=beta)
        P = coexact_projector(L)
        Hc = P @ H @ P
        lam = min_pos_eig(Hc)
        assert lam is not None
        vals.append(lam * (L**2))
    c_est = float(np.min(vals))
    assert c_est > 0.05
