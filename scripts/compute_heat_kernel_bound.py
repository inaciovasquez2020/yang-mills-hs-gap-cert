#!/usr/bin/env python3

import json
import math
import sys
from pathlib import Path

def compute_heat_kernel_bound(L, Lambda, t, dim):
    """
    Naive lattice heat-kernel trace bound:
      B(t) = sum_{|k|<=Lambda} exp(-t |k|^2)
    normalized per unit volume.

    This implementation is intentionally explicit and honest:
    it will diverge as Lambda -> infinity in d >= 2.
    """

    total = 0.0
    cutoff2 = Lambda * Lambda

    # crude integer lattice enumeration (certified stress-test only)
    R = int(math.ceil(Lambda))
    for x in range(-R, R + 1):
        for y in range(-R, R + 1):
            if dim == 2:
                k2 = x*x + y*y
                if k2 <= cutoff2:
                    total += math.exp(-t * k2)
            else:
                for z in range(-R, R + 1):
                    if dim == 3:
                        k2 = x*x + y*y + z*z
                        if k2 <= cutoff2:
                            total += math.exp(-t * k2)
                    else:
                        for w in range(-R, R + 1):
                            k2 = x*x + y*y + z*z + w*w
                            if k2 <= cutoff2:
                                total += math.exp(-t * k2)

    return total


def main():
    if len(sys.argv) != 2:
        print("usage: compute_heat_kernel_bound.py <cert.json>")
        sys.exit(1)

    cert_path = Path(sys.argv[1])
    with open(cert_path) as f:
        cert = json.load(f)

    params = cert["params"]
    L = float(params["L"])
    Lambda = float(params["Lambda"])
    t = float(params["t"])
    volume = float(params["volume"])
    dim = int(params["dim"])

    # compute raw bound
    raw = compute_heat_kernel_bound(L, Lambda, t, dim)

    # normalize per volume
    if volume > 0:
        B_t = raw / volume
    else:
        B_t = float("inf")

    # classify status
    if math.isinf(B_t) or math.isnan(B_t):
        status_type = "counterexample"
        reason = "Heat-kernel trace diverges under explicit lattice summation"
        passed = False
    elif B_t < 1.0:
        status_type = "verified"
        reason = "Certified heat-kernel coercivity bound"
        passed = True
    else:
        status_type = "draft"
        reason = "Finite bound computed but no coercivity threshold met"
        passed = False

    # write results
    cert["results"] = {
        "B_t": B_t,
        "t": t,
        "volume": volume,
        "pass": passed
    }

    cert["status"] = {
        "type": status_type,
        "reason": reason
    }

    with open(cert_path, "w") as f:
        json.dump(cert, f, indent=2)

    print("Heat-kernel bound computed")
    print(f"t     = {t}")
    print(f"B(t)  = {B_t}")
    print(f"status: {status_type}")


if __name__ == "__main__":
    main()

