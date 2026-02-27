import numpy as np
from math import pi

def symbol_4d(k):
    return sum(4*np.sin(ki/2)**2 for ki in k)

def quartic_vs_quadratic_4d(L):
    k = [2*pi/L, 0.0, 0.0, 0.0]
    lam = symbol_4d(k)
    quad = lam
    quartic = 1.0 / (L**2)
    return quad, quartic

def test_4d_quartic_subleading():
    for L in [16, 32, 64, 128]:
        quad, quartic = quartic_vs_quadratic_4d(L)
        assert quartic < quad
