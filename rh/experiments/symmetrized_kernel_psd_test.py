import numpy as np
from math import exp, pi

def phi(x, N=400):
    s = 0.0
    for n in range(1, N + 1):
        s += (2 * pi**2 * n**4 * x**2 - 3 * pi * n**2 * x) * exp(-pi * n**2 * x)
    return s

def log_grid(U=4.0, M=301):
    u = np.linspace(-U, U, M)
    du = u[1] - u[0]
    return u, du

def ksym(u, v, N=400):
    return phi(exp(u + v), N=N) + phi(exp(-(u + v)), N=N)

def kernel_matrix(u, N=400):
    M = len(u)
    K = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            K[i, j] = ksym(u[i], u[j], N=N)
    return K

def main():
    u, du = log_grid()
    K = kernel_matrix(u)
    A = du * K
    eig = np.linalg.eigvalsh(A)
    print("matrix_size", A.shape[0])
    print("min_eig", eig.min())
    print("max_eig", eig.max())
    print("psd", bool(np.all(eig >= -1e-8)))

if __name__ == "__main__":
    main()
