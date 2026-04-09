from __future__ import annotations

from scripts.run_simulated_mass_gap_proof import (
    build_certificate,
    exact_gap,
    hessian_eigenvalue,
)


def test_exact_gap_equals_mass_for_nonnegative_coupling() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert abs(cert.exact_gap - 0.75) < 1e-12


def test_zero_mode_is_minimizer() -> None:
    n = 10
    mass = 1.1
    coupling = 0.3
    assert abs(hessian_eigenvalue(n, mass, coupling, 0, 0) - exact_gap(n, mass, coupling)) < 1e-12


def test_rg_lower_bound_stays_positive() -> None:
    cert = build_certificate(
        n=6,
        mass=0.2,
        coupling=2.0,
        rg_steps=10,
        rg_scale_floor=0.85,
        rg_shift_floor=0.0,
    )
    assert cert.rg_protected_gap_lower_bound > 0.0


def test_rg_chain_stays_positive_when_shift_nonnegative() -> None:
    cert = build_certificate(
        n=6,
        mass=0.4,
        coupling=0.8,
        rg_steps=8,
        rg_scale_floor=0.95,
        rg_shift_floor=0.02,
    )
    vals = [step.outgoing_gap_lower_bound for step in cert.rg_certificates]
    assert all(v > 0.0 for v in vals)

def test_rg_gap_dominates_uniform_scale_floor_bound() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=6,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_protected_gap_lower_bound >= (0.90 ** 6) * cert.exact_gap

def test_exact_gap_is_coupling_invariant_for_nonnegative_coupling() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.6,
        coupling=0.0,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.0,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.6,
        coupling=3.5,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.0,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.6) < 1e-12

def test_zero_shift_rg_matches_iterated_scale_recurrence() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=5,
        rg_scale_floor=0.93,
        rg_shift_floor=0.0,
    )
    gap = cert.exact_gap
    for step in cert.rg_certificates:
        expected = step.scale_factor * gap
        assert abs(step.outgoing_gap_lower_bound - expected) < 1e-12
        gap = step.outgoing_gap_lower_bound

def test_smallest_mode_certificate_matches_exact_gap() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=6,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert abs(cert.mode_certificates[0].hessian_eigenvalue - cert.exact_gap) < 1e-12
    assert (cert.mode_certificates[0].k1, cert.mode_certificates[0].k2) == (0, 0)

def test_mode_certificates_are_sorted_by_hessian_eigenvalue() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=6,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    vals = [m.hessian_eigenvalue for m in cert.mode_certificates]
    assert vals == sorted(vals)

def test_rg_certificate_length_matches_steps() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=7,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 7

def test_zero_rg_steps_return_exact_gap() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap
    assert cert.rg_certificates == []

def test_exact_gap_equals_mass_case_01() -> None:
    cert = build_certificate(
        n=7,
        mass=0.25,
        coupling=0.30,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.25) < 1e-12


def test_exact_gap_equals_mass_case_02() -> None:
    cert = build_certificate(
        n=8,
        mass=0.30,
        coupling=0.60,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.30) < 1e-12


def test_exact_gap_equals_mass_case_03() -> None:
    cert = build_certificate(
        n=6,
        mass=0.35,
        coupling=0.90,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.35) < 1e-12


def test_exact_gap_equals_mass_case_04() -> None:
    cert = build_certificate(
        n=7,
        mass=0.40,
        coupling=1.20,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.40) < 1e-12


def test_exact_gap_equals_mass_case_05() -> None:
    cert = build_certificate(
        n=8,
        mass=0.45,
        coupling=1.50,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.45) < 1e-12


def test_exact_gap_equals_mass_case_06() -> None:
    cert = build_certificate(
        n=6,
        mass=0.50,
        coupling=1.80,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.50) < 1e-12


def test_exact_gap_equals_mass_case_07() -> None:
    cert = build_certificate(
        n=7,
        mass=0.55,
        coupling=2.10,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.55) < 1e-12


def test_exact_gap_equals_mass_case_08() -> None:
    cert = build_certificate(
        n=8,
        mass=0.60,
        coupling=2.40,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.60) < 1e-12


def test_exact_gap_equals_mass_case_09() -> None:
    cert = build_certificate(
        n=6,
        mass=0.65,
        coupling=2.70,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.65) < 1e-12


def test_exact_gap_equals_mass_case_10() -> None:
    cert = build_certificate(
        n=7,
        mass=0.70,
        coupling=3.00,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert abs(cert.exact_gap - 0.70) < 1e-12


def test_zero_mode_is_smallest_case_01() -> None:
    cert = build_certificate(
        n=9,
        mass=0.19,
        coupling=0.40,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_02() -> None:
    cert = build_certificate(
        n=8,
        mass=0.23,
        coupling=0.55,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_03() -> None:
    cert = build_certificate(
        n=9,
        mass=0.27,
        coupling=0.70,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_04() -> None:
    cert = build_certificate(
        n=8,
        mass=0.31,
        coupling=0.85,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_05() -> None:
    cert = build_certificate(
        n=9,
        mass=0.35,
        coupling=1.00,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_06() -> None:
    cert = build_certificate(
        n=8,
        mass=0.39,
        coupling=1.15,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_07() -> None:
    cert = build_certificate(
        n=9,
        mass=0.43,
        coupling=1.30,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_08() -> None:
    cert = build_certificate(
        n=8,
        mass=0.47,
        coupling=1.45,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_09() -> None:
    cert = build_certificate(
        n=9,
        mass=0.51,
        coupling=1.60,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_zero_mode_is_smallest_case_10() -> None:
    cert = build_certificate(
        n=8,
        mass=0.55,
        coupling=1.75,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    m0 = cert.mode_certificates[0]
    assert (m0.k1, m0.k2) == (0, 0)
    assert abs(m0.hessian_eigenvalue - cert.exact_gap) < 1e-12


def test_rg_length_matches_steps_case_01() -> None:
    cert = build_certificate(
        n=8,
        mass=0.32,
        coupling=0.50,
        rg_steps=1,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 1


def test_rg_length_matches_steps_case_02() -> None:
    cert = build_certificate(
        n=8,
        mass=0.34,
        coupling=0.60,
        rg_steps=2,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 2


def test_rg_length_matches_steps_case_03() -> None:
    cert = build_certificate(
        n=8,
        mass=0.36,
        coupling=0.70,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 3


def test_rg_length_matches_steps_case_04() -> None:
    cert = build_certificate(
        n=8,
        mass=0.38,
        coupling=0.80,
        rg_steps=4,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 4


def test_rg_length_matches_steps_case_05() -> None:
    cert = build_certificate(
        n=8,
        mass=0.40,
        coupling=0.90,
        rg_steps=5,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 5


def test_rg_length_matches_steps_case_06() -> None:
    cert = build_certificate(
        n=8,
        mass=0.42,
        coupling=1.00,
        rg_steps=6,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 6


def test_rg_length_matches_steps_case_07() -> None:
    cert = build_certificate(
        n=8,
        mass=0.44,
        coupling=1.10,
        rg_steps=7,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 7


def test_rg_length_matches_steps_case_08() -> None:
    cert = build_certificate(
        n=8,
        mass=0.46,
        coupling=1.20,
        rg_steps=8,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 8


def test_rg_length_matches_steps_case_09() -> None:
    cert = build_certificate(
        n=8,
        mass=0.48,
        coupling=1.30,
        rg_steps=9,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 9


def test_rg_length_matches_steps_case_10() -> None:
    cert = build_certificate(
        n=8,
        mass=0.50,
        coupling=1.40,
        rg_steps=10,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.rg_certificates) == 10


def test_rg_positive_chain_case_01() -> None:
    cert = build_certificate(
        n=7,
        mass=0.13,
        coupling=0.32,
        rg_steps=6,
        rg_scale_floor=0.86,
        rg_shift_floor=0.002,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_02() -> None:
    cert = build_certificate(
        n=7,
        mass=0.16,
        coupling=0.44,
        rg_steps=6,
        rg_scale_floor=0.87,
        rg_shift_floor=0.004,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_03() -> None:
    cert = build_certificate(
        n=7,
        mass=0.19,
        coupling=0.56,
        rg_steps=6,
        rg_scale_floor=0.88,
        rg_shift_floor=0.006,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_04() -> None:
    cert = build_certificate(
        n=7,
        mass=0.22,
        coupling=0.68,
        rg_steps=6,
        rg_scale_floor=0.89,
        rg_shift_floor=0.008,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_05() -> None:
    cert = build_certificate(
        n=7,
        mass=0.25,
        coupling=0.80,
        rg_steps=6,
        rg_scale_floor=0.90,
        rg_shift_floor=0.010,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_06() -> None:
    cert = build_certificate(
        n=7,
        mass=0.28,
        coupling=0.92,
        rg_steps=6,
        rg_scale_floor=0.91,
        rg_shift_floor=0.012,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_07() -> None:
    cert = build_certificate(
        n=7,
        mass=0.31,
        coupling=1.04,
        rg_steps=6,
        rg_scale_floor=0.92,
        rg_shift_floor=0.014,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_08() -> None:
    cert = build_certificate(
        n=7,
        mass=0.34,
        coupling=1.16,
        rg_steps=6,
        rg_scale_floor=0.93,
        rg_shift_floor=0.016,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_09() -> None:
    cert = build_certificate(
        n=7,
        mass=0.37,
        coupling=1.28,
        rg_steps=6,
        rg_scale_floor=0.94,
        rg_shift_floor=0.018,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_rg_positive_chain_case_10() -> None:
    cert = build_certificate(
        n=7,
        mass=0.40,
        coupling=1.40,
        rg_steps=6,
        rg_scale_floor=0.95,
        rg_shift_floor=0.020,
    )
    assert all(step.outgoing_gap_lower_bound > 0.0 for step in cert.rg_certificates)


def test_coupling_invariance_case_01() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.30,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.30,
        coupling=1.70,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.30) < 1e-12


def test_coupling_invariance_case_02() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.35,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.35,
        coupling=1.90,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.35) < 1e-12


def test_coupling_invariance_case_03() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.40,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.40,
        coupling=2.10,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.40) < 1e-12


def test_coupling_invariance_case_04() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.45,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.45,
        coupling=2.30,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.45) < 1e-12


def test_coupling_invariance_case_05() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.50,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.50,
        coupling=2.50,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.50) < 1e-12


def test_coupling_invariance_case_06() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.55,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.55,
        coupling=2.70,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.55) < 1e-12


def test_coupling_invariance_case_07() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.60,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.60,
        coupling=2.90,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.60) < 1e-12


def test_coupling_invariance_case_08() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.65,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.65,
        coupling=3.10,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.65) < 1e-12


def test_coupling_invariance_case_09() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.70,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.70,
        coupling=3.30,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.70) < 1e-12


def test_coupling_invariance_case_10() -> None:
    cert1 = build_certificate(
        n=8,
        mass=0.75,
        coupling=0.00,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    cert2 = build_certificate(
        n=8,
        mass=0.75,
        coupling=3.50,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert abs(cert1.exact_gap - cert2.exact_gap) < 1e-12
    assert abs(cert1.exact_gap - 0.75) < 1e-12

