import numpy as np

def convolution_kernel(L, sigma=1.0):
    x = np.arange(L)
    kernel = np.exp(-0.5 * (x/(L/4))**2)
    kernel = kernel / np.sum(kernel)
    return kernel

def compute_gap(L, kernel):
    C = np.zeros((L, L))
    for i in range(L):
        for j in range(L):
            C[i, j] = kernel[(i - j) % L]
    eigvals = np.linalg.eigvalsh(C)
    sorted_eigs = np.sort(eigvals)[::-1]
    gap = 1 - sorted_eigs[1] if L > 1 else 1 - sorted_eigs[0]
    return gap, sorted_eigs[:3]

def main():
    print("Convolution Gap Analysis")
    print("="*50)
    for L in [8, 16, 32, 64, 128]:
        kernel = convolution_kernel(L)
        gap, top_eigs = compute_gap(L, kernel)
        print(f"L={L:4d}, spectral gap = {gap:.6f}, top eigenvalues = {top_eigs}")

if __name__ == "__main__":
    main()
