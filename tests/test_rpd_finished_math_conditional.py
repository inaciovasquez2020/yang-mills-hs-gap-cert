import json
from pathlib import Path


def test_rpd_finished_math_conditional_snapshot_exists() -> None:
    p = Path("reports/RPD/RPD_FINISHED_MATH_CONDITIONAL_2026_04.json")
    assert p.exists()


def test_rpd_finished_math_conditional_snapshot_is_honest() -> None:
    data = json.loads(Path("reports/RPD/RPD_FINISHED_MATH_CONDITIONAL_2026_04.json").read_text())
    assert data["status"] == "conditional"
    assert data["mathematical_proof_completeness_percent_unconditional"] == 40
    assert data["mathematical_proof_completeness_percent_conditional"] == 100
    assert "eta>0" in data["blocking_unconditional_lemma"]
