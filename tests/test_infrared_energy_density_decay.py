import numpy as np
from math import pi

def transverse_symbol(kx, ky):
    sx = 2*np.sin(kx/2)
    sy = 2*np.sin(ky/2)
    return sx**2 + sy**2

def energy_density(L):
    kx = 2*pi/L
    ky = 0.0
    lam = transverse_symbol(kx, ky)
    volume = L**2
    return lam / volume

def test_ir_energy_density_decays_like_L_inv4():
    vals = []
    for L in [16, 32, 64, 128]:
        vals.append(energy_density(L))
    ratios = [vals[i+1]/vals[i] for i in range(len(vals)-1)]
    for r in ratios:
        assert r < 0.3
