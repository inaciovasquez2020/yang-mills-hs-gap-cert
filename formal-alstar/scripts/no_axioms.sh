#!/usr/bin/env bash
set -e
if grep -R -n --exclude-dir=.lake -E "axiom |sorry|admit" ALSTAR; then
  echo "Axiom or placeholder detected."
  exit 1
fi
echo "No placeholders found."
