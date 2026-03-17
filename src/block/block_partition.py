import numpy as np

def partition_indices(n, L):
    return [slice(i, min(i+L, n)) for i in range(0, n, L)]

def block_mean(g, block):
    return np.mean(g[block])

def block_variance(g, blocks):
    s = 0.0
    for b in blocks:
        m = np.mean(g[b])
        s += np.sum((g[b] - m)**2)
    return s
