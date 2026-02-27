#!/usr/bin/env bash
set -euo pipefail
pytest -q ym/vortex_mixing/tests
python3 ym/vortex_mixing/python/convolution_gap_test.py
