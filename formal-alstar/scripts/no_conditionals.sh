#!/usr/bin/env bash
set -e
if grep -R -E "Conditional|Hypothesis|Assume|Assumption" .; then
  echo "Conditional lemma detected."
  exit 1
fi
echo "No conditional lemmas found."
