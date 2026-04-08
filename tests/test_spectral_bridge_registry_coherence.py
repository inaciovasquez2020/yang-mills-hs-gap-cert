from pathlib import Path
import json

def test_spectral_bridge_registry_coherence():
    status = Path("STATUS.md").read_text()
    claims = Path("claims.yaml").read_text()
    note = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    report = json.loads(Path("reports/RPD/RPD_FINISHED_MATH_CONDITIONAL_2026_04.json").read_text())

    assert "SPECTRAL_CONTRACTION_RG | CONDITIONAL" in status
    assert "id: SPECTRAL_CONTRACTION_RG" in claims
    assert "status: conditional" in claims
    assert "CONDITIONAL" in note
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in note
    assert "eta>0" in report["blocking_unconditional_lemma"]
    assert "E_gain(u) <= (1-eta) E_main(u)" in report["blocking_unconditional_lemma"]
