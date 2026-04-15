from pathlib import Path

def test_ym_dependency_tree_2026_04() -> None:
    s = Path("docs/status/YM_DEPENDENCY_TREE_2026_04.md").read_text()
    assert "Status: CONDITIONAL" in s
    assert "YM-1" in s
    assert "YM-2" in s
    assert "BLOCK_SPECTRAL_GAP_CORE_LEMMA" in s
    assert "SPECTRAL_CONTRACTION_RG" in s
    assert "YM-3" in s
    assert "REFLECTION_POSITIVITY_SURVIVES_BLOCKING" in s
    assert "YM-4" in s
    assert "YM-5" in s
    assert "YM_MASS_GAP_ROUTE_CERTIFICATE_2026" in s
    assert "Sublemma 1 — Local Hessian Approximation" in s
    assert "Sublemma 2 — Local-to-Global Laplacian Comparison" in s
    assert "Sublemma 3 — Spectral Transfer" in s
    assert "(Sublemma 1 and Sublemma 2 and Sublemma 3 and explicit composition)" in s
