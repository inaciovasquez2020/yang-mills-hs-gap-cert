#!/usr/bin/env bash
set -e

# Reject explicit conditional language inside proofs, not theorem declarations
if grep -R -n -E "Conditional on|We assume|Assume that|Under the hypothesis that" .; then
  echo "Conditional lemma detected."
  exit 1
fi

echo "No conditional lemmas found."
