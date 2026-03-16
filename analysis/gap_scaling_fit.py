import json
import numpy as np

with open("data/gap_scaling/gap_scaling.json") as f:
    data = json.load(f)

L = np.array([d["L"] for d in data], dtype=float)
gap = np.array([d["gap"] for d in data], dtype=float)

# test scaling gap(L) ~ a + b/L
X = np.vstack([np.ones_like(L), 1.0/L]).T
coef = np.linalg.lstsq(X, gap, rcond=None)[0]

a, b = coef

print("fit: gap(L) ≈ a + b/L")
print("a =", a)
print("b =", b)

print("\npredicted infinite-volume gap:", a)
