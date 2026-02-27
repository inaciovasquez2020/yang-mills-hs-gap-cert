import numpy as np
from math import pi

def symbol_4d(k):
    return sum(4*np.sin(ki/2)**2 for ki in k)

def smallest_mode_4d(L):
    k = [2*pi/L, 0.0, 0.0, 0.0]
    return symbol_4d(k)

def test_4d_gap_closes_like_L_inv2():
    vals = []
    for L in [16, 32, 64]:
        vals.append(smallest_mode_4d(L))
    ratios = [vals[i+1]/vals[i] for i in range(len(vals)-1)]
    for r in ratios:
        assert r < 0.35
