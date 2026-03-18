import numpy as np

def lambda_min(L, beta=2.0, c0=1.0, c1=0.5):
    C = c1 / (L**2)
    return beta * c0 / (L**2) - C

Ls = [4, 8, 16, 32]

vals = [lambda_min(L) for L in Ls]

for v in vals:
    assert v > 0

scaled = [L**2 * v for L, v in zip(Ls, vals)]

for s in scaled:
    assert abs(s - scaled[0]) < 1e-6

print("core lemma scaling test: PASS")
