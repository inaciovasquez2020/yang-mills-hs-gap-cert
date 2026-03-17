import numpy as np

def block_average(f, L):
    n = len(f)
    g = np.zeros_like(f)
    for i in range(0, n, L):
        block = f[i:i+L]
        g[i:i+L] = np.mean(block)
    return g

def fluctuation_norm(f, L):
    P = block_average(f, L)
    Q = f - P
    return np.sum(Q**2)

for n in [200,400,800]:
    f = np.random.randn(n)
    for L in [10,20,40]:
        val = fluctuation_norm(f, L)
        print(n, L, val)
