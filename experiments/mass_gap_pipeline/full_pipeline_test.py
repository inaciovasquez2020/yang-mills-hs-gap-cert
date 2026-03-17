import numpy as np

def gradient_energy(g):
    return np.sum((g[1:] - g[:-1])**2)

def block_variance(g,L):
    total = 0
    for i in range(0,len(g),L):
        b = g[i:i+L]
        total += np.sum((b - np.mean(b))**2)
    return total

def run():
    n = 400
    L = 20
    trials = 5

    for t in range(trials):
        g = np.random.randn(n)
        g = g - np.mean(g)

        block_var = block_variance(g,L)
        grad = gradient_energy(g)

        print("trial",t)
        print("block variance",block_var)
        print("gradient bound",L**2 * grad)
        print("holds",block_var <= L**2 * grad)
        print("")

run()
