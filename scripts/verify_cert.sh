#!/usr/bin/env bash
set -euo pipefail

CERT="$1"

ETA=$(jq '.results.eta' "$CERT")
DELTA=$(jq '.results.delta' "$CERT")

python3 - <<PY
e=float($ETA); d=float($DELTA)
assert e+d < 1.0
print("PASS: eta+delta =", e+d)
PY
