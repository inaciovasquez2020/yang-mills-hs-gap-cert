#!/usr/bin/env python3
from pathlib import Path
import json
import sys

def main():
    paths = [
        "rg_flow/lemmas/Lem_RG_Monotonicity.json",
        "rg_flow/constructive/CONSTRUCTIVE_RGSUMMARY.md"
    ]
    ok = True
    for p in paths:
        if not Path(p).exists():
            print(f"Missing {p}")
            ok = False
    if ok:
        json.load(open("rg_flow/lemmas/Lem_RG_Monotonicity.json","r",encoding="utf-8"))
        print("RG monotonicity scaffold present")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
