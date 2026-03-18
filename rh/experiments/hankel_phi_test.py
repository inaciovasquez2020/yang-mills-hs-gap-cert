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

def g_derivative(u, k, N=200):
    x = np.exp(u)
    s = 0.0
    for n in range(1, N+1):
        a = n*n
        w = exp(-pi*a*x)
        base = (2*pi**2*a*a*x*x - 3*pi*a*x)
        val = base
        for _ in range(k):
            val = x * ((4*pi**2*a*a*x - 3*pi*a) - pi*a*val)
        s += val * w
    return s

def hankel_matrix(u, n):
    M = np.zeros((n+1, n+1))
    for i in range(n+1):
        for j in range(n+1):
            M[i, j] = g_derivative(u, i+j)
    return M

def normalize(M):
    D = np.sqrt(np.diag(M))
    return M / (D[:,None]*D[None,:])

def run_test(u, n):
    M = hankel_matrix(u, n)
    eig = np.linalg.eigvalsh(M)
    Mnorm = normalize(M)
    eign = np.linalg.eigvalsh(Mnorm)
    print(f"u={u}, n={n}")
    print("min eig:", eig.min(), "normalized min eig:", eign.min())
    return eig.min(), eign.min()

if __name__ == "__main__":
    for u in [-2,-1,0,1,2]:
        for n in [3,5,7]:
            run_test(u, n)
