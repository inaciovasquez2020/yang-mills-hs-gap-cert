#!/usr/bin/env bash
set -e
if grep -R -E "axiom|sorry|admit" .; then
  echo "Axiom or placeholder detected."
  exit 1
fi
echo "No placeholders found."
