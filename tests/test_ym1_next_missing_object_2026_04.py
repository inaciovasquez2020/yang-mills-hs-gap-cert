from pathlib import Path

def test_ym1_next_missing_object_2026_04() -> None:
    s = Path("docs/status/YM1_NEXT_MISSING_OBJECT_2026_04.md").read_text()
    shell = Path("proofs/YM1/NONABELIAN_OPERATOR_PROOF_SHELL.md").read_text()
    assert "Status: OPEN" in s
    assert "explicit non-abelian Wilson/Hamiltonian/Hessian operator on admissible gauge configurations" in s
    assert "Gauge-covariant kernel decomposition." in s
    assert "# YM-1 — Non-abelian operator" in shell
