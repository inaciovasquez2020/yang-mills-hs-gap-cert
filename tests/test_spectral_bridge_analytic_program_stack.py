from pathlib import Path

def test_spectral_bridge_analytic_program_stack():
    rel = Path("proofs/RG/analytic/RELATIVE_FORM_BOUND_PROGRAM_2026_04.md").read_text()
    hes = Path("proofs/RG/analytic/BLOCK_HESSIAN_DOMINATION_PROGRAM_2026_04.md").read_text()
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in rel
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in hes
