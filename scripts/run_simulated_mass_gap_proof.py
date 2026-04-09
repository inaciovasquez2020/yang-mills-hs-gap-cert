#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import math
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import List, Dict, Any


@dataclass
class ModeCertificate:
    k1: int
    k2: int
    laplace_eigenvalue: float
    hessian_eigenvalue: float


@dataclass
class RGStepCertificate:
    step: int
    scale_factor: float
    additive_shift: float
    incoming_gap: float
    outgoing_gap_lower_bound: float


@dataclass
class SimulatedCertificate:
    status: str
    model: str
    lattice_size: int
    mass_parameter: float
    coupling_parameter: float
    rg_steps: int
    rg_scale_floor: float
    rg_shift_floor: float
    exact_gap: float
    rg_protected_gap_lower_bound: float
    mode_certificates: List[ModeCertificate]
    rg_certificates: List[RGStepCertificate]
    theorem_statement: str
    interpretation: str
    limitations: List[str]


def laplace_eigenvalue_2d_torus(n: int, k1: int, k2: int) -> float:
    return (
        4.0 * math.sin(math.pi * k1 / n) ** 2
        + 4.0 * math.sin(math.pi * k2 / n) ** 2
    )


def hessian_eigenvalue(n: int, mass: float, coupling: float, k1: int, k2: int) -> float:
    return mass + coupling * laplace_eigenvalue_2d_torus(n, k1, k2)


def exact_gap(n: int, mass: float, coupling: float) -> float:
    values = [
        hessian_eigenvalue(n, mass, coupling, k1, k2)
        for k1 in range(n)
        for k2 in range(n)
    ]
    return min(values)


def build_mode_certificates(n: int, mass: float, coupling: float) -> List[ModeCertificate]:
    certs: List[ModeCertificate] = []
    for k1 in range(n):
        for k2 in range(n):
            lap = laplace_eigenvalue_2d_torus(n, k1, k2)
            eig = hessian_eigenvalue(n, mass, coupling, k1, k2)
            certs.append(
                ModeCertificate(
                    k1=k1,
                    k2=k2,
                    laplace_eigenvalue=lap,
                    hessian_eigenvalue=eig,
                )
            )
    certs.sort(key=lambda c: (c.hessian_eigenvalue, c.k1, c.k2))
    return certs


def build_rg_certificates(
    initial_gap: float,
    rg_steps: int,
    rg_scale_floor: float,
    rg_shift_floor: float,
) -> List[RGStepCertificate]:
    certs: List[RGStepCertificate] = []
    gap = initial_gap
    for step in range(1, rg_steps + 1):
        scale_factor = rg_scale_floor + (1.0 - rg_scale_floor) * (1.0 - math.exp(-step / 3.0))
        additive_shift = rg_shift_floor * (1.0 - math.exp(-step / 5.0))
        outgoing = scale_factor * gap + additive_shift
        certs.append(
            RGStepCertificate(
                step=step,
                scale_factor=scale_factor,
                additive_shift=additive_shift,
                incoming_gap=gap,
                outgoing_gap_lower_bound=outgoing,
            )
        )
        gap = outgoing
    return certs


def build_certificate(
    n: int,
    mass: float,
    coupling: float,
    rg_steps: int,
    rg_scale_floor: float,
    rg_shift_floor: float,
) -> SimulatedCertificate:
    if n < 2:
        raise ValueError("lattice_size must be >= 2")
    if mass <= 0.0:
        raise ValueError("mass_parameter must be > 0")
    if coupling < 0.0:
        raise ValueError("coupling_parameter must be >= 0")
    if not (0.0 < rg_scale_floor <= 1.0):
        raise ValueError("rg_scale_floor must lie in (0,1]")
    if rg_shift_floor < 0.0:
        raise ValueError("rg_shift_floor must be >= 0")
    if rg_steps < 0:
        raise ValueError("rg_steps must be >= 0")

    modes = build_mode_certificates(n, mass, coupling)
    gap = exact_gap(n, mass, coupling)
    rg_certs = build_rg_certificates(gap, rg_steps, rg_scale_floor, rg_shift_floor)
    rg_gap = rg_certs[-1].outgoing_gap_lower_bound if rg_certs else gap

    return SimulatedCertificate(
        status="SIMULATED",
        model="Abelianized Wilson–Hessian surrogate on a 2D discrete torus",
        lattice_size=n,
        mass_parameter=mass,
        coupling_parameter=coupling,
        rg_steps=rg_steps,
        rg_scale_floor=rg_scale_floor,
        rg_shift_floor=rg_shift_floor,
        exact_gap=gap,
        rg_protected_gap_lower_bound=rg_gap,
        mode_certificates=modes,
        rg_certificates=rg_certs,
        theorem_statement=(
            "For H_n = m I + beta Δ_torus with m > 0 and beta >= 0, "
            "the exact spectral gap is lambda_min(H_n) = m. "
            "Under any RG update g -> a g + b with a >= a_min > 0 and b >= 0, "
            "positivity persists and the gap remains >= a_min^s m after s steps."
        ),
        interpretation=(
            "This is an executable finite-dimensional surrogate certificate. "
            "It demonstrates the coercivity-transfer pattern but is not a proof "
            "of the non-abelian Yang–Mills mass gap."
        ),
        limitations=[
            "Finite-dimensional toy surrogate only",
            "Abelianized spectrum, not full non-abelian Wilson Hessian",
            "RG rule is imposed, not derived",
            "No continuum limit theorem",
            "No Osterwalder–Schrader reconstruction theorem is proved here",
        ],
    )


def write_markdown(cert: SimulatedCertificate, outpath: Path) -> None:
    outpath.parent.mkdir(parents=True, exist_ok=True)
    mode_lines = []
    for c in cert.mode_certificates[:12]:
        mode_lines.append(
            f"| ({c.k1},{c.k2}) | {c.laplace_eigenvalue:.12f} | {c.hessian_eigenvalue:.12f} |"
        )
    rg_lines = []
    for c in cert.rg_certificates:
        rg_lines.append(
            f"| {c.step} | {c.scale_factor:.12f} | {c.additive_shift:.12f} | "
            f"{c.incoming_gap:.12f} | {c.outgoing_gap_lower_bound:.12f} |"
        )

    text = f"""# Simulated Mass-Gap Proof Certificate

## Status
{cert.status}

## Model
{cert.model}

## Parameters
- lattice size: {cert.lattice_size}
- mass parameter: {cert.mass_parameter}
- coupling parameter: {cert.coupling_parameter}
- RG steps: {cert.rg_steps}
- RG scale floor: {cert.rg_scale_floor}
- RG shift floor: {cert.rg_shift_floor}

## Formal simulated statement
{cert.theorem_statement}

## Exact finite-volume gap
\\[
\\lambda_{{\\min}}(H_n) = {cert.exact_gap:.12f}
\\]

## RG-protected lower bound
\\[
g_{{\\mathrm{{RG}}}} \\ge {cert.rg_protected_gap_lower_bound:.12f}
\\]

## Lowest spectral modes
| mode | Laplacian eigenvalue | Hessian eigenvalue |
|---|---:|---:|
{chr(10).join(mode_lines)}

## RG chain
| step | scale factor | additive shift | incoming gap | outgoing lower bound |
|---:|---:|---:|---:|---:|
{chr(10).join(rg_lines) if rg_lines else "| 0 | 1.000000000000 | 0.000000000000 | " + f"{cert.exact_gap:.12f} | {cert.exact_gap:.12f} |"}

## Interpretation
{cert.interpretation}

## Limitations
{chr(10).join(f"- {x}" for x in cert.limitations)}
"""
    outpath.write_text(text)


def write_json(cert: SimulatedCertificate, outpath: Path) -> None:
    outpath.parent.mkdir(parents=True, exist_ok=True)
    payload: Dict[str, Any] = asdict(cert)
    outpath.write_text(json.dumps(payload, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--n", type=int, default=8)
    parser.add_argument("--mass", type=float, default=0.75)
    parser.add_argument("--coupling", type=float, default=1.25)
    parser.add_argument("--rg-steps", type=int, default=6)
    parser.add_argument("--rg-scale-floor", type=float, default=0.90)
    parser.add_argument("--rg-shift-floor", type=float, default=0.01)
    parser.add_argument(
        "--json-out",
        type=Path,
        default=Path("artifacts/simulated_mass_gap_certificate.json"),
    )
    parser.add_argument(
        "--md-out",
        type=Path,
        default=Path("proofs/simulated/SIMULATED_MASS_GAP_PROOF.md"),
    )
    args = parser.parse_args()

    cert = build_certificate(
        n=args.n,
        mass=args.mass,
        coupling=args.coupling,
        rg_steps=args.rg_steps,
        rg_scale_floor=args.rg_scale_floor,
        rg_shift_floor=args.rg_shift_floor,
    )
    write_json(cert, args.json_out)
    write_markdown(cert, args.md_out)

    print(f"status={cert.status}")
    print(f"exact_gap={cert.exact_gap:.12f}")
    print(f"rg_protected_gap_lower_bound={cert.rg_protected_gap_lower_bound:.12f}")
    print(f"json={args.json_out}")
    print(f"markdown={args.md_out}")


if __name__ == "__main__":
    main()
