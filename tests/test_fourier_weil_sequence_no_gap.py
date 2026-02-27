import numpy as np
from math import pi

def transverse_symbol(kx, ky):
    sx = 2*np.sin(kx/2)
    sy = 2*np.sin(ky/2)
    return sx**2 + sy**2

def smallest_mode(L):
    kx = 2*pi/L
    ky = 0.0
    return transverse_symbol(kx, ky)

def test_transverse_gap_closes_like_L_inv2():
    vals = []
    for L in [16, 32, 64, 128]:
        lam = smallest_mode(L)
        vals.append(lam)
    ratios = [vals[i+1]/vals[i] for i in range(len(vals)-1)]
    for r in ratios:
        assert r < 0.35
