#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

DISPROOF = Path("artifacts/disproof_of_simulated_mass_gap_proof.json")
OUT = Path("artifacts/missing_yang_mills_ingredients.json")
REPORT = Path("proofs/gap/MISSING_YANG_MILLS_INGREDIENTS.md")

INGREDIENTS = [
    {
        "id": "YM-1",
        "name": "Non-abelian operator",
        "statement": "Replace the scalar torus surrogate by an explicit non-abelian Wilson/Hamiltonian/Hessian operator on admissible gauge configurations.",
    },
    {
        "id": "YM-2",
        "name": "Gauge-invariant coercivity",
        "statement": "Prove a uniform strictly positive lower bound on the physical quotient after removal of gauge zero modes.",
    },
    {
        "id": "YM-3",
        "name": "Reflection positivity bridge",
        "statement": "Derive the positivity/coercivity statement from a bona fide Yang-Mills reflection positivity or transfer-matrix argument.",
    },
    {
        "id": "YM-4",
        "name": "Continuum transfer",
        "statement": "Prove that the lattice lower bound survives the continuum and infinite-volume limit.",
    },
    {
        "id": "YM-5",
        "name": "Mass-gap observable",
        "statement": "Identify a gauge-invariant correlator/observable whose decay is forced by the coercive lower bound.",
    },
]

def main() -> None:
    payload = json.loads(DISPROOF.read_text())
    data = {
        "source_verdict": payload["verdict"],
        "minimal_obstruction": payload["minimal_obstruction"],
        "missing_ingredients": INGREDIENTS,
        "status": "OPEN_FRONTIER",
    }
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(data, indent=2))
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(
        "# Missing Yang-Mills Ingredients\n\n"
        f"Source verdict: {data['source_verdict']}\n\n"
        f"Minimal obstruction: {data['minimal_obstruction']}\n\n"
        "## Missing ingredients\n"
        + "\n".join(f"- {x['id']}: {x['name']} — {x['statement']}" for x in INGREDIENTS)
        + "\n"
    )
    print(data["status"])
    print(OUT)
    print(REPORT)

if __name__ == "__main__":
    main()
