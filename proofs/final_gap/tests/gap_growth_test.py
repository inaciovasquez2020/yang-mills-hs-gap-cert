import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def run():
    n = 600
    L = 25

    g = np.random.randn(n)
    g = g - np.mean(g)

    lhs = np.sum(g**2)
    rhs = L**2 * gradient_energy(g)

    print("||g||^2:",lhs)
    print("L^2 grad:",rhs)
    print("bound:",lhs <= rhs)

run()
