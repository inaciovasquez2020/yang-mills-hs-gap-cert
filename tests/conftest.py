import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SW = ROOT / "tests" / "spectral_wall"

for p in (ROOT, SW):
    if str(p) not in sys.path:
        sys.path.insert(0, str(p))
