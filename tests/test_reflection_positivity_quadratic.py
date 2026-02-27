import numpy as np
from math import pi

def discrete_laplacian_symbol(kx, ky):
    return 4*np.sin(kx/2)**2 + 4*np.sin(ky/2)**2

def reflection_positive_block(L):
    for nx in range(L):
        for ny in range(L):
            kx = 2*pi*nx/L
            ky = 2*pi*ny/L
            lam = discrete_laplacian_symbol(kx, ky)
            if lam < -1e-12:
                return False
    return True

def test_quadratic_reflection_positivity():
    for L in [8, 16, 24, 32]:
        assert reflection_positive_block(L)
