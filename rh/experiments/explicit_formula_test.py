import numpy as np
from math import log, pi, sqrt
from mpmath import digamma, quad, inf, exp, sqrt as msqrt

def primes_upto(N):
    sieve = [True] * (N + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, N + 1, i):
                sieve[j] = False
    return [i for i in range(2, N + 1) if sieve[i]]

def f_hat_np(t, a):
    return np.sqrt(np.pi / a) * np.exp(-(t * t) / (4 * a))

def f_hat_mp(t, a):
    return msqrt(pi / a) * exp(-(t * t) / (4 * a))

def prime_power_sum(a, N=1000):
    primes = primes_upto(N)
    s = 0.0
    for p in primes:
        k = 1
        while p**k <= N:
            n = p**k
            s += (log(p) / sqrt(n)) * (f_hat_np(log(n), a) + f_hat_np(-log(n), a))
            k += 1
    return s

def archimedean_term(a):
    f0 = f_hat_mp(0.0, a)
    integrand = lambda t: (f0 - f_hat_mp(t, a)) / (2.0 * (exp(t/2.0) - exp(-t/2.0)) / 2.0)
    val = quad(integrand, [0, inf])
    return float(val + f0 * (log(pi) + digamma(0.25) / 2.0))

def explicit_formula_balance(a, N=1000):
    lhs = 0.0
    rhs = prime_power_sum(a, N=N) - archimedean_term(a)
    return lhs, rhs

def test():
    for a in [0.1, 0.5, 1.0, 2.0]:
        lhs, rhs = explicit_formula_balance(a)
        print("a=", a, "LHS=", lhs, "RHS=", rhs, "LHS-RHS=", lhs - rhs)

if __name__ == "__main__":
    test()
