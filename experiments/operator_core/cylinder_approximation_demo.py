import numpy as np

def cutoff(u, k):
    v = u.copy()
    v[k:] = 0
    return v

u = np.random.randn(100)

for k in [5,10,20,40]:
    approx = cutoff(u,k)
    err = np.linalg.norm(u-approx)
    print(k, err)
