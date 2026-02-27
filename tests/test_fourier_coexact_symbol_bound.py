import numpy as np
from math import pi

def lattice_symbol(L):
    ks = []
    for nx in range(L):
        for ny in range(L):
            kx = 2*pi*nx/L
            ky = 2*pi*ny/L
            ks.append((kx,ky))
    return ks

def transverse_symbol_eigenvalue(kx,ky):
    sx = 2*np.sin(kx/2)
    sy = 2*np.sin(ky/2)
    return sx**2 + sy**2

def test_uniform_lower_bound_excluding_zero_mode():
    for L in [8,12,16,20]:
        vals = []
        for kx,ky in lattice_symbol(L):
            if abs(kx)<1e-12 and abs(ky)<1e-12:
                continue
            lam = transverse_symbol_eigenvalue(kx,ky)
            vals.append(lam * (L**2))
        assert min(vals) > 1.0
