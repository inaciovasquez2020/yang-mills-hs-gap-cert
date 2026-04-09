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

