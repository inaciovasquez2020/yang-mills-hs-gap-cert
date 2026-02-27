import numpy as np
from ym.frx import (
    lazy_uniform_kernel,
    toy_confining_kernel,
    transfer_matrix_contraction_rate,
    weyl_sequence_obstruction,
)


def test_lazy_uniform_kernel_contraction():
    for m in [4, 8, 16]:
        for alpha in [0.1, 0.3, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            rate = transfer_matrix_contraction_rate(P)

            expected = 0.5 * max(np.sum(np.abs(P[i]-P[j])) for i in range(m) for j in range(m))

            print(f"m={m}, alpha={alpha}: rate={rate:.6f}, expected={expected:.6f}")
            assert abs(rate - expected) < 1e-10


def test_confining_kernel_contracts():
    for m in [8, 16, 32]:
        for g in [0.2, 0.5, 1.0]:
            W = toy_confining_kernel(m, g)

            assert not weyl_sequence_obstruction(W, tol=1e-6)

            rate = transfer_matrix_contraction_rate(W)
            print(f"m={m}, g={g}: contraction rate={rate:.6f}")
            assert rate < 1.0


def test_uniform_kernel_no_gap():
    m = 8
    W_unif = np.ones((m, m))

    rate = transfer_matrix_contraction_rate(W_unif)
    assert abs(rate - 0.0) < 1e-12

    assert not weyl_sequence_obstruction(W_unif, tol=1e-6)

def test_confining_kernel_monotone_in_g():
    m = 8
    gs = [0.2, 0.5, 1.0]
    rates = []
    for g in gs:
        W = toy_confining_kernel(m, g)
        rates.append(transfer_matrix_contraction_rate(W))
    assert rates[0] <= rates[1] <= rates[2]

def test_uniform_is_min_contraction_against_confining_family():
    m = 8
    W_unif = np.ones((m, m))
    rate_unif = transfer_matrix_contraction_rate(W_unif)

    for g in [0.2, 0.5, 1.0]:
        W = toy_confining_kernel(m, g)
        rate = transfer_matrix_contraction_rate(W)
        assert rate_unif <= rate

def test_contraction_implies_no_weyl_obstruction():
    for m in [8]:
        for g in [0.2, 0.5, 1.0]:
            W = toy_confining_kernel(m, g)
            rate = transfer_matrix_contraction_rate(W)
            if rate < 1.0:
                assert not weyl_sequence_obstruction(W, tol=1e-6)

def test_uniform_kernel_characterization():
    m = 8
    W_unif = np.ones((m, m))

    rate = transfer_matrix_contraction_rate(W_unif)
    obstruction = weyl_sequence_obstruction(W_unif, tol=1e-6)

    assert abs(rate - 0.0) < 1e-12
    assert obstruction == False


def test_contraction_implies_spectral_radius_bound():
    import numpy.linalg as la
    import numpy as np

    m = 8
    for g in [0.2, 0.5, 1.0]:
        W = toy_confining_kernel(m, g)

        row_sums = W.sum(axis=1, keepdims=True)
        P = W / row_sums

        rate = transfer_matrix_contraction_rate(P)

        eigvals = la.eigvals(P)
        spectral_radius = max(abs(eigvals))

        if rate < 1.0:
            assert spectral_radius <= 1.0 + 1e-12

def test_normalized_kernel_has_unit_top_eigenvalue_and_gap():
    import numpy as np
    import numpy.linalg as la

    m = 8
    for g in [0.2, 0.5, 1.0]:
        W = toy_confining_kernel(m, g)
        P = W / W.sum(axis=1, keepdims=True)

        eigvals = la.eigvals(P)
        mags = np.sort(np.abs(eigvals))[::-1]

        assert abs(mags[0] - 1.0) < 1e-10
        assert mags[1] < 1.0 - 1e-10

def test_second_eigenvalue_monotone_in_g():
    import numpy as np
    import numpy.linalg as la

    m = 8
    gs = [0.2, 0.5, 1.0]
    second_eigs = []

    for g in gs:
        W = toy_confining_kernel(m, g)
        P = W / W.sum(axis=1, keepdims=True)
        eigvals = la.eigvals(P)
        mags = np.sort(np.abs(eigvals))[::-1]
        second_eigs.append(mags[1])

    assert second_eigs[0] <= second_eigs[1] <= second_eigs[2]

def test_frx_gap_matches_rayleigh_probe():
    import numpy as np
    import numpy.linalg as la

    rng = np.random.default_rng(0)

    m = 16
    g = 0.5

    W = toy_confining_kernel(m, g)
    P = W / W.sum(axis=1, keepdims=True)

    eigvals = la.eigvals(P)
    mags = np.sort(np.abs(eigvals))[::-1]
    lam2 = mags[1]

    ones = np.ones(m)

    v = rng.normal(size=m)
    v = v - (v @ ones) / (ones @ ones) * ones
    v = v / la.norm(v)

    for _ in range(300):
        v = P @ v
        v = v - (v @ ones) / (ones @ ones) * ones
        nv = la.norm(v)
        if nv < 1e-12:
            break
        v = v / nv

    est = la.norm(P @ v)
    assert abs(est - lam2) < 5e-2


