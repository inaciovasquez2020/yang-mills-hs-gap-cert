import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def block_poincare_test():
    n = 200
    L = 10
    g = np.random.randn(n)

    blocks = [slice(i,i+L) for i in range(0,n,L)]

    g = g - np.mean(g)

    lhs = 0.0
    for b in blocks:
        block = g[b]
        mean = np.mean(block)
        lhs += np.sum((block-mean)**2)

    rhs = L**2 * gradient_energy(g)

    print("lhs:", lhs)
    print("rhs:", rhs)
    print("lhs <= rhs:", lhs <= rhs)

block_poincare_test()
