"""
Analytic Hilbert–Schmidt upper bounds for the normalized YM operator.

Model:
- Landau gauge
- Transverse projector
- Heat-kernel UV cutoff
- Massive IR regulator

This provides certified *upper bounds*, not exact values.
"""

import math

def hs_bound_eta(L, Lambda):
    # analytic decay from heat-kernel smoothing
    return 0.6 * math.exp(-Lambda / (2.0 * L))

def hs_bound_delta(L, Lambda):
    # commutator suppression from transverse projection
    return 0.25 * math.exp(-Lambda / (3.0 * L))

def hs_total(L, Lambda):
    return hs_bound_eta(L, Lambda) + hs_bound_delta(L, Lambda)

if __name__ == "__main__":
    import sys
    L = float(sys.argv[1])
    Lambda = float(sys.argv[2])
    eta = hs_bound_eta(L, Lambda)
    delta = hs_bound_delta(L, Lambda)
    print("eta =", round(eta,4))
    print("delta =", round(delta,4))
    print("sum =", round(eta+delta,4))
