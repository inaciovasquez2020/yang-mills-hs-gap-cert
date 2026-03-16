import numpy as np

def spectral_gap(A):
    vals = np.linalg.eigvalsh(A)
    vals = np.sort(vals)[::-1]
    return float(vals[0] - vals[1])

def generate_operator(n):
    A = np.random.randn(n,n)
    return A.T @ A

def block_operator(A):
    n = A.shape[0]//2
    B = np.zeros((n,n))
    for i in range(n):
        for j in range(n):
            block = A[2*i:2*i+2,2*j:2*j+2]
            B[i,j] = np.mean(block)
    return B

A = generate_operator(128)
for step in range(4):
    gap = spectral_gap(A)
    print("RG step",step,"size",A.shape[0],"gap",gap)
    A = block_operator(A)
