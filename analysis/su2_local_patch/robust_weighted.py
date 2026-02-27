import numpy as np
from fit_C1C2_weighted import build_forms, min_C1_for_C2

C2star = 20.0

for n in [200,320,400,520,700,900]:
    worst = 0.0
    arg = None
    for seed in range(10):
        Aform, Bform, P0 = build_forms(n=n, k=12, seed=seed)
        C1 = min_C1_for_C2(Aform, Bform, P0, C2star)
        if C1 > worst:
            worst = C1
            arg = seed
    print("n", n, "C2", C2star, "worst_C1", worst, "seed", arg)
