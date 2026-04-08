from __future__ import annotations

from pathlib import Path
import json
import yaml

STATUS = Path("proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml")
OUT = Path("reports/RPD/RPD_METRICS_2026_04.json")

WEIGHTS = {
    "proved": 1.0,
    "partial": 0.5,
    "open": 0.0,
    "blocked": 0.0,
}


def main() -> None:
    data = yaml.safe_load(STATUS.read_text())
    items = data["theorems"]

    total = len(items)
    score = 0.0
    counts = {k: 0 for k in WEIGHTS}

    for item in items:
        status = item["status"]
        counts[status] += 1
        score += WEIGHTS[status]

    out = {
        "total_theorems": total,
        "status_counts": counts,
        "mathematical_proof_completeness_percent": round(100.0 * score / total, 2),
    }

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n")
    print("PASS: RPD metrics exported")
    print(json.dumps(out, sort_keys=True))


if __name__ == "__main__":
    main()
