from pathlib import Path

def test_relative_form_bound_program_note():
    s = Path("proofs/RG/analytic/RELATIVE_FORM_BOUND_PROGRAM_2026_04.md").read_text()
    assert "theta" in s or "\\theta" in s
    assert "L_{\\mathrm{err}}" in s
    assert "L_{\\mathrm{coer}}" in s
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in s
