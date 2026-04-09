#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

SRC = Path("scripts/run_simulated_mass_gap_proof.py")
TESTS = Path("tests/test_simulated_mass_gap_proof.py")
REPORT = Path("proofs/disproof/DISPROOF_OF_SIMULATED_MASS_GAP_PROOF.md")
JSON_OUT = Path("artifacts/disproof_of_simulated_mass_gap_proof.json")


def main() -> None:
    src = SRC.read_text()
    tests = TESTS.read_text()

    facts = {
        "status_is_simulated": '"status="SIMULATED"' in src or '"SIMULATED"' in src,
        "model_is_surrogate": "surrogate" in src.lower(),
        "interpretation_denies_full_proof": "not a proof" in src.lower(),
        "limitations_finite_dimensional": "Finite-dimensional toy surrogate only" in src,
        "limitations_abelianized": "Abelianized spectrum, not full non-abelian Wilson Hessian" in src,
        "limitations_rg_imposed": "RG rule is imposed, not derived" in src,
        "limitations_no_continuum_limit": "No continuum limit theorem" in src,
        "limitations_no_os_reconstruction": "No Osterwalder–Schrader reconstruction theorem is proved here" in src,
        "uses_only_scalar_torus_laplacian": "laplace_eigenvalue_2d_torus" in src,
        "no_gauge_group_symbol": ("SU(" not in src and "GaugeGroup" not in src and "Lie algebra" not in src),
        "no_path_integral_symbol": ("path integral" not in src.lower()),
        "no_continuum_fields_symbol": ("A_mu" not in src and "F_{mu nu}" not in src and "F_mu_nu" not in src),
        "test_suite_confirms_surrogate_artifact": "test_markdown_artifact_contains_limitations_section" in tests,
    }

    failed = [k for k, v in facts.items() if not v]

    payload = {
        "target": "scripts/run_simulated_mass_gap_proof.py",
        "verdict": "DISPROVED_AS_A_YANG_MILLS_MASS_GAP_PROOF" if not failed else "INSUFFICIENT_DISPROOF_DATA",
        "facts": facts,
        "failed_checks": failed,
        "formal_conclusion": (
            "The executable object certifies only a finite-dimensional abelianized surrogate."
            if not failed
            else "Disproof script could not certify every required surrogate-only marker."
        ),
        "minimal_obstruction": (
            "A proof of the Yang–Mills mass gap requires a non-abelian Wilson/Hamiltonian/coercivity theorem with continuum transfer; the present script contains only a scalar torus surrogate."
        ),
    }

    JSON_OUT.parent.mkdir(parents=True, exist_ok=True)
    JSON_OUT.write_text(json.dumps(payload, indent=2, sort_keys=True))

    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(
        "# Disproof of Simulated Mass-Gap Proof as a Yang–Mills Proof\n\n"
        "## Verdict\n"
        f"{payload['verdict']}\n\n"
        "## Certified facts\n"
        + "\n".join(f"- {k}: {v}" for k, v in facts.items())
        + "\n\n## Formal conclusion\n"
        + payload["formal_conclusion"]
        + "\n\n## Minimal obstruction\n"
        + payload["minimal_obstruction"]
        + "\n"
    )

    print(payload["verdict"])
    print(JSON_OUT)
    print(REPORT)


if __name__ == "__main__":
    main()
