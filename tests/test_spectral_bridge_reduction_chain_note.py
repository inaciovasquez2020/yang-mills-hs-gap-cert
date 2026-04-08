from pathlib import Path

def test_spectral_bridge_reduction_chain_note():
    s = Path("proofs/RG/analytic/SPECTRAL_BRIDGE_REDUCTION_CHAIN_2026_04.md").read_text()
    assert "\\nabla^2 S_B(U)-\\beta \\Delta_B" in s
    assert "I-T_L^*T_L \\ge \\kappa(-\\Delta_G)" in s
    assert "\\|T_L f\\|\\le \\sqrt{1-\\kappa\\gamma}\\,\\|f\\|" in s
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in s
