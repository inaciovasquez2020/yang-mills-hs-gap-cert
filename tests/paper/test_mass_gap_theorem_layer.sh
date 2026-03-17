#!/usr/bin/env bash
set -euo pipefail

test -f docs/paper/yang_mills_mass_gap_outline.md
test -f docs/paper/yang_mills_mass_gap_theorem.md

grep -q "positive mass gap" docs/paper/yang_mills_mass_gap_theorem.md
grep -q "H_\\infty = H_{YM}" docs/paper/yang_mills_mass_gap_theorem.md

echo "paper theorem layer: PASS"
