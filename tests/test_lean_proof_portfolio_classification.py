from pathlib import Path
import subprocess
import sys

def test_lean_proof_portfolio_classification_exists():
    p = Path("docs/status/LEAN_PROOF_PORTFOLIO_CLASSIFICATION.md")
    assert p.exists()
    text = p.read_text(encoding="utf-8")
    assert "Portfolio class:" in text
    assert "Forbidden description" in text
    assert "Public sentence" in text

def test_lean_proof_portfolio_classification_verifier_passes():
    result = subprocess.run(
        [sys.executable, "scripts/verify_lean_proof_portfolio_classification.py"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    assert result.returncode == 0, result.stdout
