#!/usr/bin/env bash
set -e
echo "axioms:"
bash scripts/list_axioms.sh
echo "placeholders:"
grep -R -n --exclude-dir=.lake -E "sorry|admit" . || true
echo "sketch markers:"
grep -R -n --exclude-dir=.lake -E "TODO|Sketch|Claim:" ym/proofs || true
