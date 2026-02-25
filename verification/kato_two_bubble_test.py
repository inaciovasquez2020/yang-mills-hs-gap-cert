import math
import random

TWOPI2 = 2 * math.pi**2

def F_sq_radial(r, lam):
    return 192.0 * lam**4 / (r*r + lam*lam)**4

def kato_single(lam=1.0, U=50.0, N=200000):
    s = 0.0
    du = U / N
    for j in range(1, N):
        u = j * du
        s += 192.0 * u / (u*u + 1.0)**4
    return TWOPI2 * s * du

def kato_cross(lam=1.0, d=10.0, U=80.0, N=300000):
    # estimates ∫ F1·F2 / |x|^2 along a radial line
    s = 0.0
    for _ in range(N):
        r = random.random() * (U * lam)
        F1 = F_sq_radial(r, lam)
        F2 = F_sq_radial(abs(r - d), lam)
        s += math.sqrt(F1 * F2) / (r*r + 1e-12)
    return TWOPI2 * s * (U * lam) / N

single = kato_single()
print("single Kato ≈", single)
print("expected single ≈", 64 * math.pi**2)

for d in [5.0, 10.0, 20.0]:
    print("d =", d, "cross-term ≈", kato_cross(d=d))
