import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def test():
    n = 400
    L = 15
    trials = 10

    for t in range(trials):
        g = np.random.randn(n)
        g = g - np.mean(g)

        lhs = np.sum(g**2)
        rhs = L**2 * gradient_energy(g)

        print("trial",t,"bound:",lhs <= rhs)

test()
