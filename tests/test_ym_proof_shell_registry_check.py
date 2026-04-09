from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_ym_proof_shell_registry_is_complete() -> None:
    subprocess.run([sys.executable, "analysis/ym_proof_shell_registry_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_proof_shell_registry.json").read_text())
    assert payload["status"] == "PROOF_SHELL_REGISTRY_COMPLETE"


def test_ym_proof_shell_registry_has_five_entries() -> None:
    subprocess.run([sys.executable, "analysis/ym_proof_shell_registry_check.py"], check=True)
    payload = json.loads(Path("artifacts/ym_proof_shell_registry.json").read_text())
    assert payload["count_present"] == 5
    assert payload["count_required"] == 5
