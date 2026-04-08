from pathlib import Path
import json

def test_spectral_bridge_full_stack():
    root = Path("YMFormal.lean").read_text()
    hyp = Path("YMFormal/RG/SpectralBridgeHypothesis.lean").read_text()
    status = Path("STATUS.md").read_text()
    claims = Path("claims.yaml").read_text()
    note = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    report = json.loads(Path("reports/RPD/RPD_FINISHED_MATH_CONDITIONAL_2026_04.json").read_text())

    assert "import YMFormal.RG.SpectralBridgeHypothesis" in root
    assert "axiom spectral_bridge_hypothesis" in hyp
    assert "∃ η : ℝ, η > 0" in hyp
    assert "SPECTRAL_CONTRACTION_RG | CONDITIONAL" in status
    assert "id: SPECTRAL_CONTRACTION_RG" in claims
    assert "CONDITIONAL" in note
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in note
    assert report["mathematical_proof_completeness_percent_unconditional"] == 40
    assert report["mathematical_proof_completeness_percent_conditional"] == 100
