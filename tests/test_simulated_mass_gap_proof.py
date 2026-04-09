from __future__ import annotations

import math
import pytest

from scripts.run_simulated_mass_gap_proof import (
    laplace_eigenvalue_2d_torus,
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

def test_rejects_lattice_size_one() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=1, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=0.9, rg_shift_floor=0.0)


def test_rejects_nonpositive_mass_zero() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.0, coupling=1.0, rg_steps=3, rg_scale_floor=0.9, rg_shift_floor=0.0)


def test_rejects_nonpositive_mass_negative() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=-0.1, coupling=1.0, rg_steps=3, rg_scale_floor=0.9, rg_shift_floor=0.0)


def test_rejects_negative_coupling() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=-0.1, rg_steps=3, rg_scale_floor=0.9, rg_shift_floor=0.0)


def test_rejects_zero_scale_floor() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=0.0, rg_shift_floor=0.0)


def test_rejects_negative_scale_floor() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=-0.1, rg_shift_floor=0.0)


def test_rejects_scale_floor_above_one() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=1.1, rg_shift_floor=0.0)


def test_rejects_negative_shift_floor() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=0.9, rg_shift_floor=-0.01)


def test_rejects_negative_rg_steps() -> None:
    with pytest.raises(ValueError):
        build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=-1, rg_scale_floor=0.9, rg_shift_floor=0.0)


def test_accepts_boundary_scale_floor_one() -> None:
    cert = build_certificate(n=8, mass=0.5, coupling=1.0, rg_steps=3, rg_scale_floor=1.0, rg_shift_floor=0.0)
    assert cert.rg_protected_gap_lower_bound >= cert.exact_gap
def test_rg_steps_are_indexed_consecutively() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert [step.step for step in cert.rg_certificates] == [1, 2, 3, 4, 5, 6]

def test_scale_factors_stay_within_unit_interval() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=6,
        rg_scale_floor=0.87,
        rg_shift_floor=0.01,
    )
    assert all(cert.rg_scale_floor <= step.scale_factor <= 1.0 for step in cert.rg_certificates)

def test_additive_shifts_are_nonnegative() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.02,
    )
    assert all(step.additive_shift >= 0.0 for step in cert.rg_certificates)

def test_zero_shift_produces_zero_additive_terms() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.0,
    )
    assert all(abs(step.additive_shift) < 1e-12 for step in cert.rg_certificates)

def test_incoming_gap_chain_matches_previous_outgoing_gap() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert abs(cert.rg_certificates[0].incoming_gap - cert.exact_gap) < 1e-12
    for prev, curr in zip(cert.rg_certificates, cert.rg_certificates[1:]):
        assert abs(curr.incoming_gap - prev.outgoing_gap_lower_bound) < 1e-12

def test_mode_certificate_count_matches_lattice_square() -> None:
    cert = build_certificate(
        n=9,
        mass=0.5,
        coupling=1.0,
        rg_steps=4,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 81

def test_first_mode_has_zero_laplacian_eigenvalue() -> None:
    cert = build_certificate(
        n=8,
        mass=0.5,
        coupling=1.0,
        rg_steps=4,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert abs(cert.mode_certificates[0].laplace_eigenvalue) < 1e-12

def test_all_hessian_eigenvalues_dominate_mass() -> None:
    cert = build_certificate(
        n=8,
        mass=0.55,
        coupling=1.3,
        rg_steps=4,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert all(mode.hessian_eigenvalue >= cert.mass_parameter for mode in cert.mode_certificates)

def test_exact_gap_matches_minimum_mode_value() -> None:
    cert = build_certificate(
        n=8,
        mass=0.55,
        coupling=1.3,
        rg_steps=4,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert abs(cert.exact_gap - min(mode.hessian_eigenvalue for mode in cert.mode_certificates)) < 1e-12

def test_positive_shift_improves_over_pure_scaling_floor_bound() -> None:
    cert = build_certificate(
        n=8,
        mass=0.75,
        coupling=1.25,
        rg_steps=6,
        rg_scale_floor=0.9,
        rg_shift_floor=0.01,
    )
    assert cert.rg_protected_gap_lower_bound > (0.9 ** 6) * cert.exact_gap

def test_cli_writes_both_output_artifacts(tmp_path) -> None:
    import json
    import subprocess
    import sys

    json_out = tmp_path / "cert.json"
    md_out = tmp_path / "cert.md"

    subprocess.run(
        [
            sys.executable,
            "scripts/run_simulated_mass_gap_proof.py",
            "--n", "8",
            "--mass", "0.75",
            "--coupling", "1.25",
            "--rg-steps", "6",
            "--rg-scale-floor", "0.90",
            "--rg-shift-floor", "0.01",
            "--json-out", str(json_out),
            "--md-out", str(md_out),
        ],
        check=True,
    )

    assert json_out.exists()
    assert md_out.exists()

    payload = json.loads(json_out.read_text())
    assert payload["status"] == "SIMULATED"
    assert abs(payload["exact_gap"] - 0.75) < 1e-12
    assert "Simulated Mass-Gap Proof Certificate" in md_out.read_text()

def test_markdown_artifact_contains_limitations_section(tmp_path) -> None:
    import subprocess
    import sys

    json_out = tmp_path / "cert.json"
    md_out = tmp_path / "cert.md"

    subprocess.run(
        [
            sys.executable,
            "scripts/run_simulated_mass_gap_proof.py",
            "--json-out", str(json_out),
            "--md-out", str(md_out),
        ],
        check=True,
    )

    text = md_out.read_text()
    assert "## Limitations" in text
    assert "Finite-dimensional toy surrogate only" in text

def test_json_artifact_contains_required_top_level_fields(tmp_path) -> None:
    import json
    import subprocess
    import sys

    json_out = tmp_path / "cert.json"
    md_out = tmp_path / "cert.md"

    subprocess.run(
        [
            sys.executable,
            "scripts/run_simulated_mass_gap_proof.py",
            "--json-out", str(json_out),
            "--md-out", str(md_out),
        ],
        check=True,
    )

    payload = json.loads(json_out.read_text())
    required = {
        "status",
        "model",
        "lattice_size",
        "mass_parameter",
        "coupling_parameter",
        "rg_steps",
        "rg_scale_floor",
        "rg_shift_floor",
        "exact_gap",
        "rg_protected_gap_lower_bound",
        "mode_certificates",
        "rg_certificates",
        "theorem_statement",
        "interpretation",
        "limitations",
    }
    assert required.issubset(payload.keys())

def test_laplace_zero_mode_case_01() -> None:
    assert abs(laplace_eigenvalue_2d_torus(5, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_02() -> None:
    assert abs(laplace_eigenvalue_2d_torus(6, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_03() -> None:
    assert abs(laplace_eigenvalue_2d_torus(7, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_04() -> None:
    assert abs(laplace_eigenvalue_2d_torus(8, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_05() -> None:
    assert abs(laplace_eigenvalue_2d_torus(9, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_06() -> None:
    assert abs(laplace_eigenvalue_2d_torus(10, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_07() -> None:
    assert abs(laplace_eigenvalue_2d_torus(11, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_08() -> None:
    assert abs(laplace_eigenvalue_2d_torus(12, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_09() -> None:
    assert abs(laplace_eigenvalue_2d_torus(13, 0, 0)) < 1e-12


def test_laplace_zero_mode_case_10() -> None:
    assert abs(laplace_eigenvalue_2d_torus(14, 0, 0)) < 1e-12


def test_laplace_nonnegative_case_01() -> None:
    assert laplace_eigenvalue_2d_torus(6, 1, 2) >= 0.0


def test_laplace_nonnegative_case_02() -> None:
    assert laplace_eigenvalue_2d_torus(7, 2, 4) >= 0.0


def test_laplace_nonnegative_case_03() -> None:
    assert laplace_eigenvalue_2d_torus(8, 3, 6) >= 0.0


def test_laplace_nonnegative_case_04() -> None:
    assert laplace_eigenvalue_2d_torus(9, 4, 8) >= 0.0


def test_laplace_nonnegative_case_05() -> None:
    assert laplace_eigenvalue_2d_torus(10, 5, 0) >= 0.0


def test_laplace_nonnegative_case_06() -> None:
    assert laplace_eigenvalue_2d_torus(11, 6, 1) >= 0.0


def test_laplace_nonnegative_case_07() -> None:
    assert laplace_eigenvalue_2d_torus(12, 7, 2) >= 0.0


def test_laplace_nonnegative_case_08() -> None:
    assert laplace_eigenvalue_2d_torus(13, 8, 3) >= 0.0


def test_laplace_nonnegative_case_09() -> None:
    assert laplace_eigenvalue_2d_torus(14, 9, 4) >= 0.0


def test_laplace_nonnegative_case_10() -> None:
    assert laplace_eigenvalue_2d_torus(15, 10, 5) >= 0.0


def test_laplace_symmetry_swap_case_01() -> None:
    a = laplace_eigenvalue_2d_torus(7, 1, 3)
    b = laplace_eigenvalue_2d_torus(7, 3, 1)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_02() -> None:
    a = laplace_eigenvalue_2d_torus(8, 2, 6)
    b = laplace_eigenvalue_2d_torus(8, 6, 2)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_03() -> None:
    a = laplace_eigenvalue_2d_torus(9, 3, 0)
    b = laplace_eigenvalue_2d_torus(9, 0, 3)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_04() -> None:
    a = laplace_eigenvalue_2d_torus(10, 4, 2)
    b = laplace_eigenvalue_2d_torus(10, 2, 4)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_05() -> None:
    a = laplace_eigenvalue_2d_torus(11, 5, 4)
    b = laplace_eigenvalue_2d_torus(11, 4, 5)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_06() -> None:
    a = laplace_eigenvalue_2d_torus(12, 6, 6)
    b = laplace_eigenvalue_2d_torus(12, 6, 6)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_07() -> None:
    a = laplace_eigenvalue_2d_torus(13, 7, 8)
    b = laplace_eigenvalue_2d_torus(13, 8, 7)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_08() -> None:
    a = laplace_eigenvalue_2d_torus(14, 8, 10)
    b = laplace_eigenvalue_2d_torus(14, 10, 8)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_09() -> None:
    a = laplace_eigenvalue_2d_torus(15, 9, 12)
    b = laplace_eigenvalue_2d_torus(15, 12, 9)
    assert abs(a - b) < 1e-12


def test_laplace_symmetry_swap_case_10() -> None:
    a = laplace_eigenvalue_2d_torus(16, 10, 14)
    b = laplace_eigenvalue_2d_torus(16, 14, 10)
    assert abs(a - b) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_01() -> None:
    lap = laplace_eigenvalue_2d_torus(8, 1, 4)
    eig = hessian_eigenvalue(8, 0.13, 0.27, 1, 4)
    assert abs(eig - (0.13 + 0.27 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_02() -> None:
    lap = laplace_eigenvalue_2d_torus(9, 2, 8)
    eig = hessian_eigenvalue(9, 0.16, 0.34, 2, 8)
    assert abs(eig - (0.16 + 0.34 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_03() -> None:
    lap = laplace_eigenvalue_2d_torus(10, 3, 2)
    eig = hessian_eigenvalue(10, 0.19, 0.41, 3, 2)
    assert abs(eig - (0.19 + 0.41 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_04() -> None:
    lap = laplace_eigenvalue_2d_torus(11, 4, 5)
    eig = hessian_eigenvalue(11, 0.22, 0.48, 4, 5)
    assert abs(eig - (0.22 + 0.48 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_05() -> None:
    lap = laplace_eigenvalue_2d_torus(12, 5, 8)
    eig = hessian_eigenvalue(12, 0.25, 0.55, 5, 8)
    assert abs(eig - (0.25 + 0.55 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_06() -> None:
    lap = laplace_eigenvalue_2d_torus(13, 6, 11)
    eig = hessian_eigenvalue(13, 0.28, 0.62, 6, 11)
    assert abs(eig - (0.28 + 0.62 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_07() -> None:
    lap = laplace_eigenvalue_2d_torus(14, 7, 0)
    eig = hessian_eigenvalue(14, 0.31, 0.69, 7, 0)
    assert abs(eig - (0.31 + 0.69 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_08() -> None:
    lap = laplace_eigenvalue_2d_torus(15, 8, 2)
    eig = hessian_eigenvalue(15, 0.34, 0.76, 8, 2)
    assert abs(eig - (0.34 + 0.76 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_09() -> None:
    lap = laplace_eigenvalue_2d_torus(16, 9, 4)
    eig = hessian_eigenvalue(16, 0.37, 0.83, 9, 4)
    assert abs(eig - (0.37 + 0.83 * lap)) < 1e-12


def test_hessian_matches_mass_plus_coupling_times_laplace_case_10() -> None:
    lap = laplace_eigenvalue_2d_torus(17, 10, 6)
    eig = hessian_eigenvalue(17, 0.40, 0.90, 10, 6)
    assert abs(eig - (0.40 + 0.90 * lap)) < 1e-12


def test_exact_gap_function_equals_mass_case_01() -> None:
    assert abs(exact_gap(6, 0.22, 0.11) - 0.22) < 1e-12


def test_exact_gap_function_equals_mass_case_02() -> None:
    assert abs(exact_gap(7, 0.26, 0.22) - 0.26) < 1e-12


def test_exact_gap_function_equals_mass_case_03() -> None:
    assert abs(exact_gap(8, 0.30, 0.33) - 0.30) < 1e-12


def test_exact_gap_function_equals_mass_case_04() -> None:
    assert abs(exact_gap(9, 0.34, 0.44) - 0.34) < 1e-12


def test_exact_gap_function_equals_mass_case_05() -> None:
    assert abs(exact_gap(10, 0.38, 0.55) - 0.38) < 1e-12


def test_exact_gap_function_equals_mass_case_06() -> None:
    assert abs(exact_gap(11, 0.42, 0.66) - 0.42) < 1e-12


def test_exact_gap_function_equals_mass_case_07() -> None:
    assert abs(exact_gap(12, 0.46, 0.77) - 0.46) < 1e-12


def test_exact_gap_function_equals_mass_case_08() -> None:
    assert abs(exact_gap(13, 0.50, 0.88) - 0.50) < 1e-12


def test_exact_gap_function_equals_mass_case_09() -> None:
    assert abs(exact_gap(14, 0.54, 0.99) - 0.54) < 1e-12


def test_exact_gap_function_equals_mass_case_10() -> None:
    assert abs(exact_gap(15, 0.58, 1.10) - 0.58) < 1e-12

def test_theorem_statement_mentions_exact_gap_case_01() -> None:
    cert = build_certificate(
        n=8,
        mass=0.23,
        coupling=0.10,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_02() -> None:
    cert = build_certificate(
        n=8,
        mass=0.26,
        coupling=0.20,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_03() -> None:
    cert = build_certificate(
        n=8,
        mass=0.29,
        coupling=0.30,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_04() -> None:
    cert = build_certificate(
        n=8,
        mass=0.32,
        coupling=0.40,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_05() -> None:
    cert = build_certificate(
        n=8,
        mass=0.35,
        coupling=0.50,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_06() -> None:
    cert = build_certificate(
        n=8,
        mass=0.38,
        coupling=0.60,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_07() -> None:
    cert = build_certificate(
        n=8,
        mass=0.41,
        coupling=0.70,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_08() -> None:
    cert = build_certificate(
        n=8,
        mass=0.44,
        coupling=0.80,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_09() -> None:
    cert = build_certificate(
        n=8,
        mass=0.47,
        coupling=0.90,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_theorem_statement_mentions_exact_gap_case_10() -> None:
    cert = build_certificate(
        n=8,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.91,
        rg_shift_floor=0.00,
    )
    assert "exact spectral gap is lambda_min(H_n) = m" in cert.theorem_statement


def test_interpretation_declares_surrogate_case_01() -> None:
    cert = build_certificate(
        n=7,
        mass=0.27,
        coupling=0.15,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_02() -> None:
    cert = build_certificate(
        n=7,
        mass=0.29,
        coupling=0.30,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_03() -> None:
    cert = build_certificate(
        n=7,
        mass=0.31,
        coupling=0.45,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_04() -> None:
    cert = build_certificate(
        n=7,
        mass=0.33,
        coupling=0.60,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_05() -> None:
    cert = build_certificate(
        n=7,
        mass=0.35,
        coupling=0.75,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_06() -> None:
    cert = build_certificate(
        n=7,
        mass=0.37,
        coupling=0.90,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_07() -> None:
    cert = build_certificate(
        n=7,
        mass=0.39,
        coupling=1.05,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_08() -> None:
    cert = build_certificate(
        n=7,
        mass=0.41,
        coupling=1.20,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_09() -> None:
    cert = build_certificate(
        n=7,
        mass=0.43,
        coupling=1.35,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_interpretation_declares_surrogate_case_10() -> None:
    cert = build_certificate(
        n=7,
        mass=0.45,
        coupling=1.50,
        rg_steps=4,
        rg_scale_floor=0.92,
        rg_shift_floor=0.01,
    )
    assert "finite-dimensional surrogate certificate" in cert.interpretation


def test_limitations_have_expected_length_case_01() -> None:
    cert = build_certificate(
        n=6,
        mass=0.31,
        coupling=0.25,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_02() -> None:
    cert = build_certificate(
        n=6,
        mass=0.32,
        coupling=0.30,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_03() -> None:
    cert = build_certificate(
        n=6,
        mass=0.33,
        coupling=0.35,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_04() -> None:
    cert = build_certificate(
        n=6,
        mass=0.34,
        coupling=0.40,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_05() -> None:
    cert = build_certificate(
        n=6,
        mass=0.35,
        coupling=0.45,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_06() -> None:
    cert = build_certificate(
        n=6,
        mass=0.36,
        coupling=0.50,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_07() -> None:
    cert = build_certificate(
        n=6,
        mass=0.37,
        coupling=0.55,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_08() -> None:
    cert = build_certificate(
        n=6,
        mass=0.38,
        coupling=0.60,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_09() -> None:
    cert = build_certificate(
        n=6,
        mass=0.39,
        coupling=0.65,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_limitations_have_expected_length_case_10() -> None:
    cert = build_certificate(
        n=6,
        mass=0.40,
        coupling=0.70,
        rg_steps=2,
        rg_scale_floor=0.93,
        rg_shift_floor=0.00,
    )
    assert len(cert.limitations) == 5


def test_mode_certificate_count_case_01() -> None:
    cert = build_certificate(
        n=5,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 25


def test_mode_certificate_count_case_02() -> None:
    cert = build_certificate(
        n=6,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 36


def test_mode_certificate_count_case_03() -> None:
    cert = build_certificate(
        n=7,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 49


def test_mode_certificate_count_case_04() -> None:
    cert = build_certificate(
        n=8,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 64


def test_mode_certificate_count_case_05() -> None:
    cert = build_certificate(
        n=9,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 81


def test_mode_certificate_count_case_06() -> None:
    cert = build_certificate(
        n=10,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 100


def test_mode_certificate_count_case_07() -> None:
    cert = build_certificate(
        n=11,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 121


def test_mode_certificate_count_case_08() -> None:
    cert = build_certificate(
        n=12,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 144


def test_mode_certificate_count_case_09() -> None:
    cert = build_certificate(
        n=13,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 169


def test_mode_certificate_count_case_10() -> None:
    cert = build_certificate(
        n=14,
        mass=0.50,
        coupling=1.00,
        rg_steps=3,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert len(cert.mode_certificates) == 196


def test_zero_step_chain_empty_case_01() -> None:
    cert = build_certificate(
        n=8,
        mass=0.22,
        coupling=0.12,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_02() -> None:
    cert = build_certificate(
        n=8,
        mass=0.26,
        coupling=0.24,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_03() -> None:
    cert = build_certificate(
        n=8,
        mass=0.30,
        coupling=0.36,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_04() -> None:
    cert = build_certificate(
        n=8,
        mass=0.34,
        coupling=0.48,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_05() -> None:
    cert = build_certificate(
        n=8,
        mass=0.38,
        coupling=0.60,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_06() -> None:
    cert = build_certificate(
        n=8,
        mass=0.42,
        coupling=0.72,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_07() -> None:
    cert = build_certificate(
        n=8,
        mass=0.46,
        coupling=0.84,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_08() -> None:
    cert = build_certificate(
        n=8,
        mass=0.50,
        coupling=0.96,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_09() -> None:
    cert = build_certificate(
        n=8,
        mass=0.54,
        coupling=1.08,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap


def test_zero_step_chain_empty_case_10() -> None:
    cert = build_certificate(
        n=8,
        mass=0.58,
        coupling=1.20,
        rg_steps=0,
        rg_scale_floor=0.90,
        rg_shift_floor=0.01,
    )
    assert cert.rg_certificates == []
    assert cert.rg_protected_gap_lower_bound == cert.exact_gap

