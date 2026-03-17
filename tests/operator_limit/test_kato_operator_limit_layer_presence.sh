#!/usr/bin/env bash
set -euo pipefail

test -f proofs/operator_limit/derivations/kato_closed_form_conditions.md
test -f proofs/operator_limit/derivations/monotone_form_convergence.md
test -f proofs/operator_limit/derivations/strong_resolvent_theorem_application.md
test -f proofs/operator_limit/derivations/cylinder_core_density.md
test -f proofs/operator_limit/derivations/yang_mills_operator_identification.md

grep -q "closed" proofs/operator_limit/derivations/kato_closed_form_conditions.md
grep -q "q_L \\\uparrow q_\\infty" proofs/operator_limit/derivations/monotone_form_convergence.md
grep -q "xrightarrow{s.r.}" proofs/operator_limit/derivations/strong_resolvent_theorem_application.md
grep -q "D_{\\\\mathrm{cyl}}" proofs/operator_limit/derivations/cylinder_core_density.md
grep -q "H_\\infty = H_{YM}" proofs/operator_limit/derivations/yang_mills_operator_identification.md

echo "kato/operator-limit proof layer presence: PASS"
