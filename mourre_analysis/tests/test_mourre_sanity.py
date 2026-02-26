#!/usr/bin/env python3
from pathlib import Path
import json
import sys

def main():
    paths = [
        "mourre_analysis/notes/MOURRE_DERIVATION_PLAN.md",
        "mourre_analysis/derivations/commutator_calculus.md",
        "mourre_analysis/lemmas/Lem_Mourre_C1.json",
        "mourre_analysis/lemmas/Lem_Mourre_PositiveFree.json",
        "mourre_analysis/lemmas/Lem_Mourre_BoundedPerturb.json",
    ]
    ok = True
    for p in paths:
        if not Path(p).exists():
            print(f"Missing {p}")
            ok = False
    if ok:
        for p in paths:
            if p.endswith(".json"):
                json.load(open(p, "r", encoding="utf-8"))
        print("Mourre derivation scaffold present")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
