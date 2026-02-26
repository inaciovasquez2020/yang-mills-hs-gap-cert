import numpy as np

def gaussian_cov(m, k):
    return 1.0 / (k*k + m*m)

def hs_norm(m, cutoff=50):
    k = np.linspace(-cutoff, cutoff, 20001)
    dk = k[1]-k[0]
    return np.sum((gaussian_cov(m,k))**2) * dk

for m in [0.5, 1.0, 2.0]:
    print("Gaussian HS norm m=", m, hs_norm(m))

print("Nonabelian case: no Gaussian reference available (conceptual obstruction).")
