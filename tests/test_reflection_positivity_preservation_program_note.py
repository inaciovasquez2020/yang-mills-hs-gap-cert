from pathlib import Path

def test_reflection_positivity_preservation_program_note():
    s = Path("proofs/RG/analytic/REFLECTION_POSITIVITY_PRESERVATION_PROGRAM_2026_04.md").read_text()
    assert "\\mathcal R\\ge 0" in s
    assert "\\mathcal R_L\\ge 0" in s
    assert "REFLECTION\\_POSITIVITY\\_SURVIVES\\_BLOCKING" in s
