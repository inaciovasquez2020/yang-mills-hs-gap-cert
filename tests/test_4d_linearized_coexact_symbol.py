import numpy as np
from math import pi

def symbol_4d(k):
    return sum(4*np.sin(ki/2)**2 for ki in k)

def scaled_min_4d(L):
    vals = []
    for n1 in range(L):
        for n2 in range(L):
            for n3 in range(L):
                for n4 in range(L):
                    if n1==0 and n2==0 and n3==0 and n4==0:
                        continue
                    k = [2*pi*n1/L, 2*pi*n2/L, 2*pi*n3/L, 2*pi*n4/L]
                    lam = symbol_4d(k)
                    vals.append(lam * L**2)
    return min(vals)

def test_4d_linearized_scaled_constant():
    target = 4*pi*pi
    for L in [8, 12, 16]:
        cL = scaled_min_4d(L)
        rel = abs(cL - target)/target
        assert rel < 0.15
