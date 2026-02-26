#!/usr/bin/env python3
from pathlib import Path
import sys

def main():
    paths = [
        "counterexamples/notes/COUNTEREXAMPLE_STRESS_PLAN.md",
        "counterexamples/stress/stress_matrix.md",
        "counterexamples/constructors/flux_tube_candidate.md",
        "counterexamples/constructors/scaling_candidate.md",
    ]
    ok = True
    for p in paths:
        if not Path(p).exists():
            print(f"Missing {p}")
            ok = False
    if ok:
        print("Counterexample stress scaffold present")
    return 0 if ok else 1

if __name__ == "__main__":
    sys.exit(main())
