#!/usr/bin/env bash
set -e
grep -R -n --exclude-dir=.lake "axiom " formal-alstar/ALSTAR || true
