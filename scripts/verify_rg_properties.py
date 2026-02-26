#!/usr/bin/env python3
import json
from pathlib import Path

def check(path):
    if not Path(path).exists():
        print(f"Missing: {path}")
        return False
    print(f"Found: {path}")
    return True

def main():
    ok = True
    ok &= check("rg_flow/explicit_intertwiner.json")
    ok &= check("mourre_analysis/uniform_mourre_constant.json")
    ok &= check("os_reconstruction/os_positivity_preservation.json")
    ok &= check("counterexamples/violation_analysis.json")
    if ok:
        print("RG framework files present")
    else:
        print("Some files missing")
    return 0 if ok else 1

if __name__ == "__main__":
    raise SystemExit(main())
