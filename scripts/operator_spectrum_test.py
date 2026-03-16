import numpy as np

def generate_operator(n):
    A = np.random.randn(n,n)
    return A.T @ A

def spectrum(A):
    vals = np.linalg.eigvalsh(A)
    return np.sort(vals)[::-1]

A = generate_operator(64)
vals = spectrum(A)

print("top eigenvalues:", vals[:5])
print("gap:", vals[0]-vals[1])
