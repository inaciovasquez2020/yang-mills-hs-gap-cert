import numpy as np

def gaussian_throughput_bound(m, cutoff=50):
    k = np.linspace(-cutoff, cutoff, 20001)
    dk = k[1] - k[0]
    integrand = 1.0 / (k**2 + m**2)**2
    return np.sum(integrand) * dk

for m in [0.5, 1.0, 2.0]:
    val = gaussian_throughput_bound(m)
    print(f"m={m}, HS_bound={val}")
