set -euo pipefail
python3 -m pip -q install --upgrade pip
python3 -m pip -q install pytest
pytest -q ym/vortex_mixing/tests
python3 ym/vortex_mixing/python/convolution_gap_test.py | head -n 80
