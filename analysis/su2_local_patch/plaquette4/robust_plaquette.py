import numpy as np
from fit_plaquette_C1C2 import grid_search

for k in [12,16,24]:
    for n in [320,400,520,700,900]:
        worstC1 = 0.0
        arg = None
        for seed in range(10):
            C1, C2 = grid_search(n=n, k=k, seed=seed, C2max=50.0, m=1001)
            if C1 > worstC1:
                worstC1 = C1
                arg = (seed, C2)
        print("k", k, "n", n, "worstC1", worstC1, "at", arg)
