from pathlib import Path

def test_relative_form_bound_program_links_to_open_bridge():
    note = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    program = Path("proofs/RG/analytic/RELATIVE_FORM_BOUND_PROGRAM_2026_04.md").read_text()
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in note
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in program
