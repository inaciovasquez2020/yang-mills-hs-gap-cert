#!/usr/bin/env python3
from pathlib import Path
import sys

def main():
    p = Path("counterexamples/stress/C2_commutator_failure_targets.md")
    if not p.exists():
        print("Missing counterexamples/stress/C2_commutator_failure_targets.md")
        return 1
    print("C2 stress target file present")
    return 0

if __name__ == "__main__":
    sys.exit(main())
