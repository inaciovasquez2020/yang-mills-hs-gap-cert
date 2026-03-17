import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)
