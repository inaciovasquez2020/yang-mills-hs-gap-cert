import numpy as np
from scripts.hs_gap_spectrum import hs_gap

def generate_transfer_matrix(n):
    A = np.random.randn(n,n)
    return A.T @ A

for n in [32,64,128]:
    K = generate_transfer_matrix(n)
    gap,_ = hs_gap(K)
    print("size:", n, "gap:", gap)
