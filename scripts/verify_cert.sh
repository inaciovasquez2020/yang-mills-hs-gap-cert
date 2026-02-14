#!/usr/bin/env bash
set -euo pipefail

CERT="$1"

TYPE=$(jq -r '.status.type' "$CERT")
ETA=$(jq -r '.results.eta' "$CERT")
DELTA=$(jq -r '.results.delta' "$CERT")
SUM=$(jq -r '.results.sum' "$CERT")

if [[ "$TYPE" != "verified" && "$TYPE" != "counterexample" ]]; then
  echo "FAIL: invalid status.type = $TYPE"
  exit 1
fi

if [[ "$ETA" == "null" || "$DELTA" == "null" || "$SUM" == "null" ]]; then
  echo "FAIL: missing HS bounds"
  exit 1
fi

echo "PASS: status=$TYPE eta+delta=$SUM"
exit 0

