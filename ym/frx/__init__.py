"""
FRX contraction normalization:

dobrushin_tv_contraction(P) and transfer_matrix_contraction_rate(P)
implement the classical Dobrushin coefficient

    ρ(P) = (1/2) * max_{i,j} ||P_i - P_j||_1

All FRX tests are written against this normalization.
"""
from .transfer_matrix import (
    row_stochasticize,
    lazy_uniform_kernel,
    dobrushin_tv_contraction,
    transfer_matrix_contraction_rate,
    toy_confining_kernel,
    weyl_sequence_obstruction
)

__all__ = [
    'row_stochasticize',
    'lazy_uniform_kernel',
    'dobrushin_tv_contraction',
    'transfer_matrix_contraction_rate',
    'toy_confining_kernel',
    'weyl_sequence_obstruction'
]


"""
FRX Structural Certification (Test-Backed)

Certified invariants (see tests):

1. Normalization:
   ρ(P) = (1/2) * max_{i,j} ||P_i - P_j||_1

2. Equality:
   transfer_matrix_contraction_rate(P) == dobrushin_tv_contraction(P)

3. Monotonicity:
   - Lazy uniform kernel: ρ is monotone in α
   - Confining kernel: contraction is monotone in g

4. Spectral Bridge:
   contraction_rate(W) < 1  ⇒  no Weyl obstruction

5. Uniform baseline:
   Uniform kernel has rate = 0 and no obstruction.

This block is invariant-guarded by the FRX test suite.
"""

def empirical_gap_vs_contraction_constant(m: int = 16, g_grid=None) -> float:
    """
    Empirical bridge constant for the toy confining family:

        1 - |λ2(P)| >= c_emp * (1 - ρ(P))

    where P is the row-normalized kernel from toy_confining_kernel(m, g),
    ρ is transfer_matrix_contraction_rate(P), and λ2 is the second-largest
    eigenvalue magnitude of P.

    This is a numerical diagnostic, not a proof certificate.
    """
    import numpy as np
    import numpy.linalg as la

    if g_grid is None:
        g_grid = np.linspace(0.1, 1.5, 8)

    ratios = []

    for g in g_grid:
        W = toy_confining_kernel(m, float(g))
        P = W / W.sum(axis=1, keepdims=True)

        rho = transfer_matrix_contraction_rate(P)

        eigvals = la.eigvals(P)
        mags = np.sort(np.abs(eigvals))[::-1]
        lam2 = mags[1]

        gap = 1.0 - float(lam2)
        contraction_defect = 1.0 - float(rho)

        if contraction_defect > 1e-12:
            ratios.append(gap / contraction_defect)

    if not ratios:
        return 0.0

    return float(min(ratios))
