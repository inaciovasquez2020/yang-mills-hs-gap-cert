import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def block_poincare(g, L):
    n = len(g)
    total = 0.0
    for i in range(0,n,L):
        block = g[i:i+L]
        mean = np.mean(block)
        total += np.sum((block-mean)**2)
    return total

def run():
    n = 400
    L = 20

    g = np.random.randn(n)
    g = g - np.mean(g)

    lhs = block_poincare(g,L)
    rhs = L**2 * gradient_energy(g)

    print("block variance:", lhs)
    print("gradient bound:", rhs)
    print("inequality satisfied:", lhs <= rhs)

run()
