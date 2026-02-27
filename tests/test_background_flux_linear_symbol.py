import numpy as np
from math import pi

def shifted_symbol(kx, ky, theta):
    sx = 2*np.sin((kx+theta)/2)
    sy = 2*np.sin((ky+theta)/2)
    return sx**2 + sy**2

def min_scaled_shifted(L, theta):
    vals = []
    for nx in range(L):
        for ny in range(L):
            kx = 2*pi*nx/L
            ky = 2*pi*ny/L
            if nx == 0 and ny == 0:
                continue
            lam = shifted_symbol(kx, ky, theta)
            vals.append(lam * (L**2))
    return min(vals)

def test_flux_background_linear_symbol_scaled_constant_O1():
    for L in [16, 32, 64]:
        theta = 2*pi/(L*L)
        cL = min_scaled_shifted(L, theta)
        assert cL > 20.0
