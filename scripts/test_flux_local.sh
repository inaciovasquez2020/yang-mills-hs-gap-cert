set -e

repo_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$repo_root"

test -f inputs/FLUX/FLUX.tex

grep -n 'begin{assumption}\[FLUX\]' inputs/FLUX/FLUX.tex >/dev/null
grep -n 'Tightness from FLUX' inputs/FLUX/FLUX.tex >/dev/null
grep -n 'lower semicontinuity' inputs/FLUX/FLUX.tex >/dev/null
grep -n 'Final Wall' inputs/FLUX/FLUX.tex >/dev/null

python3 -m py_compile tests/toy/toy_flux_gaussian_wall.py
python3 tests/toy/toy_flux_gaussian_wall.py

echo "PASS: FLUX local tests"
