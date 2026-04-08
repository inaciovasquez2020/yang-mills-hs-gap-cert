from pathlib import Path

REQUIRED = [
    "proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml",
    "proofs/RPD/RPD_TARGETS_2026_04.md",
    "templates/RPD/RPD_PROOF_SHELLS_2026_04.md",
    "open_problems/RPD_ERROR_GAIN_LEMMA.md",
    "registries/rpd/RPD_AXIOM_MAP_2026_04.yaml",
]

def test_rpd_proof_shell_files_exist() -> None:
    missing = [p for p in REQUIRED if not Path(p).exists()]
    assert not missing, f"missing required RPD proof-shell files: {missing}"
