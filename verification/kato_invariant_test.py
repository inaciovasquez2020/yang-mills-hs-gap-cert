import math

TWOPI2 = 2 * math.pi**2

def kato(U=50.0, N=200000):
    s = 0.0
    du = U / N
    for j in range(1, N):
        u = j * du
        s += 192.0 * u / (u*u + 1.0)**4
    return TWOPI2 * s * du

expected = 64 * math.pi**2
val = kato()
for lam in [1.0, 0.5, 0.1, 0.01]:
    print(lam, val, " expected ", expected)
