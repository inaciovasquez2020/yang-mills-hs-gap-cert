#!/usr/bin/env bash
set -euo pipefail

test -f proofs/poincare/cube_product_spectrum.md
test -f proofs/poincare/tensor_product_laplacian.md
test -f proofs/poincare/cube_gap_tensor_derivation.md

test -f proofs/analytic_replacements/derivations/block_poincare_derivation.md
test -f proofs/analytic_replacements/derivations/block_projection_operator.md
test -f proofs/analytic_replacements/derivations/cycle_support_localization_derivation.md

test -f proofs/operator_limit/derivations/kato_closed_form_conditions.md
test -f proofs/operator_limit/derivations/strong_resolvent_theorem_application.md
test -f proofs/operator_limit/derivations/yang_mills_operator_identification.md

echo "YM gap certificate pipeline structure: PASS"
