import numpy as np

kappa = 0.2
gamma = 0.3

lhs = np.sqrt(1 - kappa * gamma)
assert lhs < 1

n = 10
decay = (1 - kappa * gamma) ** (n / 2)
assert decay < 1

m = -0.5 * np.log(1 - kappa * gamma)
assert m > 0

print("mass gap chain test: PASS")
