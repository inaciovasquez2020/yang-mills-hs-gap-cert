from pathlib import Path

def test_root_imports_spectral_bridge_hypothesis():
    s = Path("YMFormal.lean").read_text()
    assert "import YMFormal.RG.SpectralBridgeHypothesis" in s
