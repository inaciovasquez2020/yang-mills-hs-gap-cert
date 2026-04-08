from pathlib import Path

def test_reflection_positivity_analytic_stack():
    rp = Path("proofs/RG/analytic/REFLECTION_POSITIVITY_PRESERVATION_PROGRAM_2026_04.md").read_text()
    assert "\\mathcal R\\ge 0" in rp
    assert "\\mathcal R_L\\ge 0" in rp
    assert "REFLECTION\\_POSITIVITY\\_SURVIVES\\_BLOCKING" in rp
