import numpy as np
from math import pi

def symbol_4d(k):
    return sum(4*np.sin(ki/2)**2 for ki in k)

def reflection_positive_4d(L):
    for n1 in range(L):
        for n2 in range(L):
            for n3 in range(L):
                for n4 in range(L):
                    k = [2*pi*n1/L, 2*pi*n2/L, 2*pi*n3/L, 2*pi*n4/L]
                    lam = symbol_4d(k)
                    if lam < -1e-12:
                        return False
    return True

def test_4d_quadratic_reflection_positivity():
    for L in [4, 6, 8]:
        assert reflection_positive_4d(L)
