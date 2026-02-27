import numpy as np
from fit_C1C2_weighted import build_forms, min_C1_for_C2

C2star = 2.2

for k in [8,12,16,24]:
    worst = 0.0
    arg = None
    for seed in range(10):
        Aform, Bform, P0 = build_forms(n=700, k=k, seed=seed)
        C1 = min_C1_for_C2(Aform, Bform, P0, C2star)
        if C1 > worst:
            worst = C1
            arg = seed
    print("k", k, "C2", C2star, "worst_C1", worst, "seed", arg)
