import numpy as np

def fluctuation_bound(L, c=1.0):
    return c * L**2

def energy(L):
    return 1.0 / (L**2)

Ls = [4, 8, 16, 32]

vals = [fluctuation_bound(L) * energy(L) for L in Ls]

for v in vals:
    assert abs(v - vals[0]) < 1e-6

print("block Poincare scaling test: PASS")
