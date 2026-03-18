import numpy as np
from math import exp, pi

def phi(x, N=400):
    s = 0.0
    for n in range(1, N + 1):
        s += (2 * pi**2 * n**4 * x**2 - 3 * pi * n**2 * x) * exp(-pi * n**2 * x)
    return s

def log_grid(U=4.0, M=401):
    u = np.linspace(-U, U, M)
    x = np.exp(u)
    du = u[1] - u[0]
    return u, x, du

def kernel_matrix(x, N=400):
    M = len(x)
    K = np.zeros((M, M))
    for i in range(M):
        for j in range(M):
            K[i, j] = phi(x[i] * x[j], N=N)
    return K

def quadratic_form(K, f, du):
    return du * du * float(f @ (K @ f))

def basis_functions(u):
    return {
        "gaussian_0": np.exp(-u * u),
        "gaussian_1": u * np.exp(-u * u),
        "gaussian_2": (u * u - 1.0) * np.exp(-u * u),
        "left_bump": np.exp(-(u + 1.5) ** 2 / 0.3),
        "right_bump": np.exp(-(u - 1.5) ** 2 / 0.3),
        "oscillatory": np.cos(3.0 * u) * np.exp(-0.5 * u * u),
    }

def main():
    u, x, du = log_grid()
    K = kernel_matrix(x)
    vals = []
    for name, f in basis_functions(u).items():
        q = quadratic_form(K, f, du)
        vals.append((name, q))
        print(name, q)
    min_name, min_q = min(vals, key=lambda t: t[1])
    print("minimum_test_value", min_name, min_q)

if __name__ == "__main__":
    main()
