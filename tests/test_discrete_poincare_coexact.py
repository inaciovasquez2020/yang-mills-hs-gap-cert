import numpy as np
from math import pi

def discrete_laplacian_symbol(kx, ky):
    return 4*np.sin(kx/2)**2 + 4*np.sin(ky/2)**2

def min_scaled_symbol(L):
    vals = []
    for nx in range(L):
        for ny in range(L):
            if nx == 0 and ny == 0:
                continue
            kx = 2*pi*nx/L
            ky = 2*pi*ny/L
            lam = discrete_laplacian_symbol(kx, ky)
            vals.append(lam * (L**2))
    return min(vals)

def test_discrete_poincare_constant_lower_bound():
    for L in [16, 24, 32, 48, 64]:
        cL = min_scaled_symbol(L)
        assert cL > 30.0
