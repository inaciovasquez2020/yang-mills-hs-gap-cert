from pathlib import Path

def test_transfer_operator_analytic_stack():
    rel = Path("proofs/RG/analytic/RELATIVE_FORM_BOUND_PROGRAM_2026_04.md").read_text()
    hes = Path("proofs/RG/analytic/BLOCK_HESSIAN_DOMINATION_PROGRAM_2026_04.md").read_text()
    trn = Path("proofs/RG/analytic/TRANSFER_OPERATOR_CONTRACTION_PROGRAM_2026_04.md").read_text()
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in rel
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in hes
    assert "I-T_L^*T_L \\ge \\kappa(-\\Delta_G)" in trn
    assert "\\|T_L f\\|\\le \\sqrt{1-\\kappa\\gamma}\\,\\|f\\|" in trn
