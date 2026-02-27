import numpy as np
from math import pi

def transverse_symbol(kx, ky):
    sx = 2*np.sin(kx/2)
    sy = 2*np.sin(ky/2)
    return sx**2 + sy**2

def su2_linear_min_scaled(L):
    vals = []
    for nx in range(L):
        for ny in range(L):
            if nx == 0 and ny == 0:
                continue
            kx = 2*pi*nx/L
            ky = 2*pi*ny/L
            lam = transverse_symbol(kx, ky)
            vals.append(lam * (L**2))
    return min(vals)

def test_su2_linear_transverse_constant():
    target = 4*pi*pi
    for L in [16, 24, 32, 48]:
        cL = su2_linear_min_scaled(L)
        rel_err = abs(cL - target) / target
        assert rel_err < 0.15
