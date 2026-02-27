import numpy as np
from fit_C1C2_weighted import build_forms, min_C1_for_C2

Aform, Bform, P0 = build_forms(n=400, k=12, seed=0)

center = 2.2
width = 2.0
m = 8001

bestC1 = np.inf
bestC2 = None
for C2 in np.linspace(max(0.0, center-width), center+width, m):
    C1 = min_C1_for_C2(Aform, Bform, P0, float(C2))
    if C1 < bestC1:
        bestC1 = C1
        bestC2 = float(C2)

print("local_best_C2:", bestC2)
print("local_best_C1:", bestC1)
