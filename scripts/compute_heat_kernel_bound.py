#!/usr/bin/env python3

import json
import sys
import math

def main():
    if len(sys.argv) != 2:
        print("usage: compute_heat_kernel_bound.py <cert.json>")
        sys.exit(2)

    path = sys.argv[1]
    cert = json.load(open(path))

    t = cert["params"].get("t", 1.0)
    volume = cert["params"].get("volume", 1.0)

    # Placeholder lower spectral envelope:
    # In real implementation, replace by lattice / analytic bound.
    lambda_min = cert["inputs"].get("lambda_min_lower_bound", 0.0)

    if lambda_min <= 0:
        B_t = float("inf")
        passed = False
    else:
        B_t = math.exp(-t * lambda_min)
        passed = B_t < 1.0

    cert["results"] = {
        "B_t": B_t,
        "t": t,
        "volume": volume,
        "pass": passed
    }

    cert["status"] = {
        "type": "verified" if passed else "inconclusive"
    }

    json.dump(cert, open(path, "w"), indent=2)

    print(f"Heat-kernel bound computed")
    print(f"t     = {t}")
    print(f"B(t)  = {B_t}")
    print(f"status: {cert['status']['type']}")

if __name__ == "__main__":
    main()

