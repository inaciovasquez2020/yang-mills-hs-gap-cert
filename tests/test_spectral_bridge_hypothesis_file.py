from pathlib import Path

def test_spectral_bridge_hypothesis_file_exists():
    p = Path("YMFormal/RG/SpectralBridgeHypothesis.lean")
    assert p.exists()
    s = p.read_text()
    assert "axiom spectral_bridge_hypothesis" in s
    assert "∃ η : ℝ, η > 0" in s
