import numpy as np

def hs_gap(matrix):
    eigvals = np.linalg.eigvalsh(matrix)
    eigvals = np.sort(eigvals)[::-1]
    gap = eigvals[0] - eigvals[1]
    return gap, eigvals

if __name__ == "__main__":
    np.random.seed(0)
    A = np.random.randn(50,50)
    K = A.T @ A
    gap, eigvals = hs_gap(K)
    print("top eigenvalues:", eigvals[:5])
    print("spectral gap:", gap)
