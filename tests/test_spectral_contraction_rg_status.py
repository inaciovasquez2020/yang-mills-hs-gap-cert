from pathlib import Path
import json

def test_status_marks_spectral_contraction_rg_conditional():
    s = Path("STATUS.md").read_text()
    assert "SPECTRAL_CONTRACTION_RG | CONDITIONAL" in s

def test_claims_registry_contains_spectral_contraction_rg():
    s = Path("claims.yaml").read_text()
    assert "SPECTRAL_CONTRACTION_RG" in s

def test_rpd_json_records_exact_open_blocking_lemma():
    data = json.loads(Path("reports/RPD/RPD_FINISHED_MATH_CONDITIONAL_2026_04.json").read_text())
    lemma = data["blocking_unconditional_lemma"]
    assert "eta>0" in lemma
    assert "E_gain(u) <= (1-eta) E_main(u)" in lemma
    assert "actual Yang-Mills operator/data path" in lemma
    assert data["mathematical_proof_completeness_percent_unconditional"] == 40
    assert data["mathematical_proof_completeness_percent_conditional"] == 100
