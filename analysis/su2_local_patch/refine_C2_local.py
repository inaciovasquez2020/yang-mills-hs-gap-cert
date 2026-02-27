import numpy as np
from fit_C1C2 import build_mats, min_C1_for_C2

L, V, P0 = build_mats(n=400, k=12, seed=0)

center = 20.0
width = 5.0
m = 4001

bestC1 = np.inf
bestC2 = None
for C2 in np.linspace(center-width, center+width, m):
    C1 = min_C1_for_C2(L, V, P0, float(C2))
    if C1 < bestC1:
        bestC1 = C1
        bestC2 = float(C2)

print("local_best_C2:", bestC2)
print("local_best_C1:", bestC1)
