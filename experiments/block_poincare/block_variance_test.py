import numpy as np

def block_means(g, blocks):
    means = []
    for b in blocks:
        means.append(np.mean(g[b]))
    return means

def variance_decomposition(g, blocks):
    total = np.sum(g**2)
    rhs = 0.0
    for b in blocks:
        block = g[b]
        mean = np.mean(block)
        rhs += np.sum((block - mean)**2)
    return total, rhs

def run():
    n = 200
    g = np.random.randn(n)

    blocks = []
    L = 10
    for i in range(0,n,L):
        blocks.append(slice(i,i+L))

    g = g - np.mean(g)

    total, rhs = variance_decomposition(g, blocks)

    print("||g||^2:", total)
    print("block variance sum:", rhs)

run()
