import json
from pathlib import Path


def test_rpd_final_frontier_files_exist() -> None:
    assert Path("open_problems/RPD/RPD_FINAL_FRONTIER_2026_04.md").exists()
    assert Path("reports/RPD/RPD_REMAINING_COMPLETION_2026_04.json").exists()


def test_rpd_remaining_completion_snapshot() -> None:
    data = json.loads(Path("reports/RPD/RPD_REMAINING_COMPLETION_2026_04.json").read_text())
    assert data["organizational_closure_percent"] == 100
    assert data["mathematical_proof_completeness_percent"] == 40
    assert "RPD_ERROR_GAIN_LEMMA" in data["sole_missing_ingredient"] or "Yang-Mills" in data["sole_missing_ingredient"]
