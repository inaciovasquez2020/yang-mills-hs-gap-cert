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
