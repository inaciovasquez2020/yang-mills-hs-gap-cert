import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def operator_gap(g,L):
    lhs = np.sum(g**2)
    rhs = L**2 * gradient_energy(g)
    return lhs,rhs

def run():
    n = 500
    L = 20

    g = np.random.randn(n)
    g = g - np.mean(g)

    lhs,rhs = operator_gap(g,L)

    print("||g||^2:",lhs)
    print("L^2 grad:",rhs)
    print("spectral bound:",lhs <= rhs)

run()
