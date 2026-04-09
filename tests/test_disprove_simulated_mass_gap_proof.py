from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def test_disproof_script_emits_verdict(tmp_path) -> None:
    subprocess.run([sys.executable, "analysis/disprove_simulated_mass_gap_proof.py"], check=True)
    payload = json.loads(Path("artifacts/disproof_of_simulated_mass_gap_proof.json").read_text())
    assert payload["verdict"] == "DISPROVED_AS_A_YANG_MILLS_MASS_GAP_PROOF"


def test_disproof_certifies_surrogate_only_markers() -> None:
    subprocess.run([sys.executable, "analysis/disprove_simulated_mass_gap_proof.py"], check=True)
    payload = json.loads(Path("artifacts/disproof_of_simulated_mass_gap_proof.json").read_text())
    assert payload["facts"]["status_is_simulated"] is True
    assert payload["facts"]["model_is_surrogate"] is True
    assert payload["facts"]["interpretation_denies_full_proof"] is True


def test_disproof_certifies_missing_nonabelian_content() -> None:
    subprocess.run([sys.executable, "analysis/disprove_simulated_mass_gap_proof.py"], check=True)
    payload = json.loads(Path("artifacts/disproof_of_simulated_mass_gap_proof.json").read_text())
    assert payload["facts"]["limitations_abelianized"] is True
    assert payload["facts"]["uses_only_scalar_torus_laplacian"] is True
    assert payload["facts"]["no_gauge_group_symbol"] is True


def test_disproof_certifies_missing_continuum_bridge() -> None:
    subprocess.run([sys.executable, "analysis/disprove_simulated_mass_gap_proof.py"], check=True)
    payload = json.loads(Path("artifacts/disproof_of_simulated_mass_gap_proof.json").read_text())
    assert payload["facts"]["limitations_no_continuum_limit"] is True
    assert payload["facts"]["limitations_no_os_reconstruction"] is True
    assert payload["facts"]["limitations_rg_imposed"] is True


def test_disproof_report_contains_formal_conclusion() -> None:
    subprocess.run([sys.executable, "analysis/disprove_simulated_mass_gap_proof.py"], check=True)
    text = Path("proofs/disproof/DISPROOF_OF_SIMULATED_MASS_GAP_PROOF.md").read_text()
    assert "DISPROVED_AS_A_YANG_MILLS_MASS_GAP_PROOF" in text
    assert "finite-dimensional abelianized surrogate" in text
