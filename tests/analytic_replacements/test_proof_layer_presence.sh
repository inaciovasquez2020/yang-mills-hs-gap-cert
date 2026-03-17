#!/usr/bin/env bash
set -euo pipefail

test -f proofs/analytic_replacements/block_poincare_reduction.md
test -f proofs/analytic_replacements/fluctuation_projection_decomposition.md
test -f proofs/analytic_replacements/cycle_localization_theorem.md

echo "analytic replacement proof-layer presence: PASS"
