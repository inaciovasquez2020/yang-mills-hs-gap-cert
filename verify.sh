#!/usr/bin/env bash
set -e

echo "=== LEAN BUILD ==="
if command -v lake >/dev/null 2>&1; then
  lake build
fi

echo "=== PYTHON CHECK ==="
python3 -m py_compile $(git ls-files '*.py')

if [ -f "pytest.ini" ] || [ -d "tests" ]; then
  pytest -q
fi

echo "=== CERTIFICATE PHASE ==="
python3 tools/make_cert.py > cert.json
python3 tools/verify_cert.py cert.json

echo "=== DONE ==="
