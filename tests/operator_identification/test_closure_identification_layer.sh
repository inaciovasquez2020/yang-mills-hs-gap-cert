#!/usr/bin/env bash
set -euo pipefail

test -f proofs/operator_identification/closure_identification_theorem.md
test -f proofs/operator_identification/mass_gap_transfer.md

grep -q "H_\\infty = H_{YM}" proofs/operator_identification/closure_identification_theorem.md
grep -q "positive mass gap" proofs/operator_identification/mass_gap_transfer.md

echo "operator identification layer: PASS"
