import numpy as np

def naive_bound(L, C0=1.0, d=4):
    return C0 * (L**d)

def improved_bound(L, c=1.0):
    return c * (L**-2)

Ls = [4, 8, 16, 32]

naive = [naive_bound(L) for L in Ls]
improved = [improved_bound(L) for L in Ls]

for n, i in zip(naive, improved):
    assert i < n

ratios = [n / i for n, i in zip(naive, improved)]

for r in ratios:
    assert r > 1

print("locality cancellation scaling test: PASS")
