import numpy as np
from math import exp, pi

def phi(x, N=200):
    s = 0.0
    for n in range(1, N+1):
        s += (2*pi**2*n**4*x**2 - 3*pi*n**2*x) * exp(-pi*n**2*x)
    return s

def g(u):
    return phi(np.exp(u))

def derivative(u, k, h=1e-5):
    if k == 0:
        return g(u)
    if k == 1:
        return (g(u+h) - g(u-h)) / (2*h)
    if k == 2:
        return (g(u+h) - 2*g(u) + g(u-h)) / (h*h)
    if k == 3:
        return (g(u+2*h) - 2*g(u+h) + 2*g(u-h) - g(u-2*h)) / (2*h**3)
    if k == 4:
        return (g(u+2*h) - 4*g(u+h) + 6*g(u) - 4*g(u-h) + g(u-2*h)) / (h**4)
    raise ValueError("k too large")

def hankel_matrix(u, n):
    M = np.zeros((n+1, n+1))
    for i in range(n+1):
        for j in range(n+1):
            M[i, j] = derivative(u, i+j)
    return M

def test_hankel(u=0.0, n=3):
    M = hankel_matrix(u, n)
    eig = np.linalg.eigvalsh(M)
    print("Hankel matrix:\n", M)
    print("Eigenvalues:", eig)
    return np.all(eig >= -1e-8)

if __name__ == "__main__":
    ok = test_hankel()
    print("Hankel PSD:", ok)
