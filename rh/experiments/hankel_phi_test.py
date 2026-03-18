import numpy as np
from math import exp, pi

def phi_terms(u, N=200):
    x = np.exp(u)
    terms = []
    for n in range(1, N+1):
        a = n*n
        w = exp(-pi*a*x)
        terms.append((a, x, w))
    return terms

def g(u):
    s = 0.0
    for a, x, w in phi_terms(u):
        s += (2*pi**2*a*a*x*x - 3*pi*a*x) * w
    return s

def g_derivative(u, k, N=200):
    x = np.exp(u)
    s = 0.0
    for n in range(1, N+1):
        a = n*n
        w = exp(-pi*a*x)
        base = (2*pi**2*a*a*x*x - 3*pi*a*x)
        val = base
        for _ in range(k):
            val = x * ( (4*pi**2*a*a*x - 3*pi*a) - pi*a*val )
        s += val * w
    return s

def hankel_matrix(u, n):
    M = np.zeros((n+1, n+1))
    for i in range(n+1):
        for j in range(n+1):
            M[i, j] = g_derivative(u, i+j)
    return M

def test_hankel(u=0.0, n=3):
    M = hankel_matrix(u, n)
    eig = np.linalg.eigvalsh(M)
    print("Hankel matrix:\n", M)
    print("Eigenvalues:", eig)
    return np.all(eig >= -1e-6)

if __name__ == "__main__":
    ok = test_hankel()
    print("Hankel PSD:", ok)
