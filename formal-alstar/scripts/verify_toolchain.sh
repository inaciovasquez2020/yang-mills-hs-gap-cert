#!/usr/bin/env bash
set -e

EXPECTED=$(cat lean-toolchain)
CURRENT=$(lean --version | head -n1 | awk '{print $3}')

echo "Expected toolchain: $EXPECTED"
echo "Installed version: $CURRENT"

if [[ "$CURRENT" != *"$EXPECTED"* ]]; then
  echo "Toolchain mismatch"
  exit 1
fi

echo "Toolchain OK"
