from pathlib import Path

def test_block_hessian_program_links_to_bridge_target():
    hessian = Path("proofs/RG/analytic/BLOCK_HESSIAN_DOMINATION_PROGRAM_2026_04.md").read_text()
    bridge = Path("proofs/RG/SPECTRAL_BRIDGE_MINIMAL_OPEN_LEMMA_2026_04.md").read_text()
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)E_{\\mathrm{main}}(u)" in hessian
    assert "E_{\\mathrm{gain}}(u)\\le (1-\\eta)\\,E_{\\mathrm{main}}(u)" in bridge
