import numpy as np

def correlation_length(eigs):
    eigs = np.sort(eigs)[::-1]
    if eigs[1] <= 0:
        return float("inf")
    return -1.0/np.log(eigs[1]/eigs[0])

A = np.random.randn(64,64)
K = A.T @ A
vals = np.linalg.eigvalsh(K)
xi = correlation_length(vals)
print("correlation length:",xi)
