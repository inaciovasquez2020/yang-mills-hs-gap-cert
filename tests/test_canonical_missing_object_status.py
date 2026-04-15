from pathlib import Path

def test_canonical_missing_object_locked():
    p = Path("docs/status/CANONICAL_MISSING_OBJECT.md")
    s = p.read_text()
    assert "Status: OPEN" in s
    assert "`BLOCK_SPECTRAL_GAP_CORE_LEMMA`" in s
    assert "SPECTRAL_CONTRACTION_RG" in s
    assert "YM_MASS_GAP_ROUTE_CERTIFICATE_2026" in s

def test_core_lemma_is_unique_earliest_blocker():
    core = Path("docs/status/CORE_LEMMA.md").read_text()
    dep = Path("docs/status/DEPENDENCY_GRAPH.md").read_text()
    assert "Only this lemma blocks unconditional proof" in core
    assert "Only the Core Lemma remains open" in dep
