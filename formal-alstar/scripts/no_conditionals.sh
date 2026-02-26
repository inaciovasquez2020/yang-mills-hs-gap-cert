#!/usr/bin/env bash
set -e
if grep -R -n --exclude-dir=.lake -E "Conditional on|We assume|Assume that|Under the hypothesis that" ALSTAR; then
  echo "Conditional lemma detected."
  exit 1
fi
echo "No conditional lemmas found."
