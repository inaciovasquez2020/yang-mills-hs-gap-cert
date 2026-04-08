from pathlib import Path

REQUIRED = [
    "proofs/RPD/theorems/RPD_4_KERNEL_PRESERVATION.md",
    "proofs/RPD/theorems/RPD_5A_PULSE_TO_LAMBDAMIN_ZERO.md",
    "proofs/RPD/theorems/RPD_5B_ZERO_MODE_TO_NONCOERCIVE.md",
    "proofs/RPD/theorems/RPD_6_TWO_BUBBLE_INCOMPATIBILITY.md",
    "proofs/RPD/theorems/RPD_ERROR_GAIN_LEMMA.md",
    "proofs/RPD/RPD_PROOF_STATUS_2026_04.yaml",
    "proofs/RPD/RPD_TARGETS_2026_04.md",
]

def test_rpd_theorem_target_files_exist() -> None:
    missing = [p for p in REQUIRED if not Path(p).exists()]
    assert not missing, f"missing required RPD theorem-target files: {missing}"
