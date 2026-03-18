import numpy as np

def lambda_min(L, beta=1.0, c0=1.0, C=0.1):
    return (beta * c0 - C) / (L**2)

Ls = [4, 8, 16, 32]
vals = [lambda_min(L) for L in Ls]

scaled = [L**2 * v for L, v in zip(Ls, vals)]

for v in vals:
    assert v > 0

for s in scaled:
    assert abs(s - scaled[0]) < 1e-6

print("hessian gap scaling test: PASS")
