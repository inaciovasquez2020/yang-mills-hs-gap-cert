#!/usr/bin/env bash
set -euo pipefail

test -f proofs/operator_limit/kato_form_convergence.md
test -f proofs/operator_limit/cylinder_core_identification.md

echo "operator-limit proof-layer presence: PASS"
