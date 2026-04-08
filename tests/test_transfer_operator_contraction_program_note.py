from pathlib import Path

def test_transfer_operator_contraction_program_note():
    s = Path("proofs/RG/analytic/TRANSFER_OPERATOR_CONTRACTION_PROGRAM_2026_04.md").read_text()
    assert "I-T_L^*T_L \\ge \\kappa(-\\Delta_G)" in s
    assert "\\|T_L f\\|\\le \\sqrt{1-\\kappa\\gamma}\\,\\|f\\|" in s
