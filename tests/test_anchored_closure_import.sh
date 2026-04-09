#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake env lean YMFormal/AnchoredClosure.lean
