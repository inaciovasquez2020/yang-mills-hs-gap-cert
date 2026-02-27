import numpy as np
from math import pi

def transverse_symbol(kx, ky):
    sx = 2*np.sin(kx/2)
    sy = 2*np.sin(ky/2)
    return sx**2 + sy**2

def quartic_energy_scale(L):
    kx = 2*pi/L
    ky = 0.0
    lam = transverse_symbol(kx, ky)
    amp = 1.0
    quad = lam * amp**2
    quartic = (amp**4) / (L**2)
    return quad, quartic

def test_quartic_subleading_to_quadratic():
    for L in [16, 32, 64, 128]:
        quad, quartic = quartic_energy_scale(L)
        assert quartic < quad
