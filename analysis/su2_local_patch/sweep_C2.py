import numpy as np
from fit_C1C2 import build_mats, min_C1_for_C2

L, V = build_mats(n=400, k=12, seed=0)

def sweep(C2max, m):
    bestC1 = np.inf
    bestC2 = None
    for C2 in np.linspace(0.0, C2max, m):
        C1 = min_C1_for_C2(L, V, float(C2))
        if C1 < bestC1:
            bestC1 = C1
            bestC2 = float(C2)
    return bestC1, bestC2

for C2max in [10.0, 20.0, 50.0, 100.0, 200.0]:
    C1, C2 = sweep(C2max, 401)
    print("C2max", C2max, "bestC2", C2, "bestC1", C1)
