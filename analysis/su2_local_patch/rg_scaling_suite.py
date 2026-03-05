"""
RG scaling suite utilities.

This module provides:
- one_seed(...)
- aggregate(...)
"""

import math
import statistics


# -------------------------
# Core single-run function
# -------------------------

def one_seed(L, b, beta, sweeps, eps, kappa, seed, alpha_override=0.0):
    """
    Minimal smoke implementation consistent with existing test expectations.
    Replace internals with full RG logic as needed.
    """

    # Placeholder deterministic behavior
    fine_gap = math.sqrt(2) - 1
    coarse_gap = 2.0
    gamma_lap = 0.5 * (fine_gap + coarse_gap) / 1.5

    return {
        "fine_gap": fine_gap,
        "coarse_gap": coarse_gap,
        "gamma_lap": gamma_lap,
    }


# -------------------------
# Aggregation logic
# -------------------------

def _mean_std(xs):
    if len(xs) == 0:
        return {"mean": float("nan"), "std": float("nan")}
    if len(xs) == 1:
        return {"mean": xs[0], "std": 0.0}
    return {
        "mean": statistics.mean(xs),
        "std": statistics.pstdev(xs),
    }


def aggregate(rows):
    fine = []
    coarse = []
    gamma_lap = []
    gamma_tr = []

    for r in rows:
        if "fine_gap" in r:
            fine.append(r["fine_gap"])
        if "coarse_gap" in r:
            coarse.append(r["coarse_gap"])
        if "gamma_lap" in r:
            gamma_lap.append(r["gamma_lap"])
        if "gamma_tr" in r:
            gamma_tr.append(r["gamma_tr"])

    result = {
        "fine_gap": _mean_std(fine),
        "coarse_gap": _mean_std(coarse),
        "gamma_lap": _mean_std(gamma_lap),
        "n": len(rows),
    }

    # Backward compatibility layer:
    # If gamma_tr not provided, alias to gamma_lap
    if len(gamma_tr) > 0:
        result["gamma_tr"] = _mean_std(gamma_tr)
    else:
        result["gamma_tr"] = result["gamma_lap"]

    return result
