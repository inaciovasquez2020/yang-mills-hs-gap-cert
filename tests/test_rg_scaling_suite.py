import json, os, math
import numpy as np
from analysis.su2_local_patch.rg_scaling_suite import one_seed, aggregate

def test_rg_gamma_smoke_fast():
    L = 8
    b = 2
    beta = 2.3
    sweeps = 4
    eps = 0.25
    kappa = 1.0
    seeds = [1,2,3]

    rows = [one_seed(L,b,beta,sweeps,eps,kappa,sd,alpha_override=0.0) for sd in seeds]
    agg = aggregate(rows)

    g = agg["gamma_lap"]["mean"]
    assert math.isfinite(g)
    assert 0.2 <= g <= 3.0

    gt = agg["gamma_tr"]["mean"]
    assert math.isfinite(gt)
    assert -1.0 <= gt <= 3.0
