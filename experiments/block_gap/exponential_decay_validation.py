import numpy as np

kappa = 0.2
gamma = 0.3
m = -0.5 * np.log(1 - kappa * gamma)

def corr(r):
    return np.exp(-m * r)

rs = [1, 2, 5, 10, 20]

vals = [corr(r) for r in rs]

for i in range(len(vals)-1):
    assert vals[i] > vals[i+1]

print("exponential decay test: PASS")
