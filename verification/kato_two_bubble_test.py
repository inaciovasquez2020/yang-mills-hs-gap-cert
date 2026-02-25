import math
import random

TWOPI2 = 2 * math.pi**2

def F_sq_radial(r, lam, shift):
    # x = (r,0,0,0); shift = (d,0,0,0)
    rr = r - shift
    r2 = rr*rr
    return 192.0 * lam**4 / (r2 + lam*lam)**4

def kato_two(lam=1.0, d=10.0, U=80.0, N=300000):
    # 1D radial-line Monte Carlo proxy for additivity sanity check
    # (not a full 4D Monte Carlo; intended as a quick regression test)
    s = 0.0
    for _ in range(N):
        r = random.random() * (U * lam)
        F = F_sq_radial(r, lam, 0.0) + F_sq_radial(r, lam, d)
        s += F / (r*r + 1e-12)
    return TWOPI2 * s * (U * lam) / N

expected_single = 64 * math.pi**2
for d in [5.0, 10.0, 20.0]:
    print("d =", d, " Kato_two ≈", kato_two(lam=1.0, d=d), " target ≈", 2*expected_single)
