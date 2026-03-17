import numpy as np

def random_field(n):
    return np.random.randn(n)

def discrete_gradient_energy(f):
    return np.sum((f[1:] - f[:-1])**2)

for L in [50,100,200,400]:
    f = random_field(L)
    var = np.sum((f - np.mean(f))**2)
    grad = discrete_gradient_energy(f)
    ratio = var / grad if grad > 0 else 0
    print(L, ratio)
