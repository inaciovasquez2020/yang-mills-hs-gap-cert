from pathlib import Path

def test_transfer_operator_program_links_to_bridge_target():
    transfer = Path("proofs/RG/analytic/TRANSFER_OPERATOR_CONTRACTION_PROGRAM_2026_04.md").read_text()
    bridge = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    assert "I-T_L^*T_L \\ge \\kappa(-\\Delta_G)" in transfer
    assert "\\|T_L f\\|\\le \\sqrt{1-\\kappa\\gamma}\\,\\|f\\|" in transfer
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in bridge
