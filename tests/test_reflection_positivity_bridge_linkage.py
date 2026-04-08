from pathlib import Path

def test_reflection_positivity_program_links_to_status_target():
    note = Path("proofs/RG/analytic/REFLECTION_POSITIVITY_PRESERVATION_PROGRAM_2026_04.md").read_text()
    status = Path("STATUS.md").read_text()
    assert "REFLECTION\\_POSITIVITY\\_SURVIVES\\_BLOCKING" in note
    assert "REFLECTION_POSITIVITY_SURVIVES_BLOCKING | CONDITIONAL" in status
