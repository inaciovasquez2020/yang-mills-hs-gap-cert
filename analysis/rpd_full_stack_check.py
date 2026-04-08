from __future__ import annotations

import subprocess
import sys

CHECKS = [
    ["analysis/rpd_gap_chain.py"],
    ["analysis/rpd_registry_check.py"],
    ["analysis/rpd_proof_status_check.py"],
    ["analysis/rpd_theorem_target_check.py"],
    ["analysis/rpd_manifest_check.py"],
    ["analysis/rpd_dashboard_check.py"],
    ["analysis/rpd_status_consistency_check.py"],
    ["analysis/rpd_manifest_status_sync_check.py"],
    ["analysis/rpd_blocking_check.py"],
    ["analysis/rpd_status_progress_check.py"],
    ["proofs/RPD/executable/rpd_4_kernel_preservation_check.py"],
    ["proofs/RPD/executable/rpd_5a_pulse_to_lambdamin_zero_check.py"],
    ["proofs/RPD/executable/rpd_5b_zero_mode_to_noncoercive_check.py"],
    ["proofs/RPD/executable/rpd_6_two_bubble_incompatibility_check.py"],
    ["proofs/RPD/executable/rpd_error_gain_lemma_check.py"],
]


def main() -> None:
    for check in CHECKS:
        proc = subprocess.run([sys.executable, *check], check=False)
        if proc.returncode != 0:
            raise SystemExit(proc.returncode)
    print("PASS: RPD full stack verified")


if __name__ == "__main__":
    main()
