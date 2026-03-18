import numpy as np
from math import log, pi, sqrt

def primes_upto(N):
    sieve = [True] * (N + 1)
    sieve[0] = sieve[1] = False
    for i in range(2, int(N**0.5) + 1):
        if sieve[i]:
            for j in range(i * i, N + 1, i):
                sieve[j] = False
    return [i for i in range(2, N + 1) if sieve[i]]

def hat_f(t, T):
    at = abs(t)
    if at >= T:
        return 0.0
    return 1.0 - at / T

def archimedean_term(T, U=2000, A=40.0):
    ts = np.linspace(1e-6, A, U)
    vals = []
    f0 = hat_f(0.0, T)
    for t in ts:
        num = f0 - hat_f(t, T)
        den = 2.0 * np.sinh(t / 2.0)
        vals.append(num / den)
    integral = np.trapezoid(vals, ts)
    return integral + f0 * log(pi)

def prime_power_sum(T, N=5000):
    s = 0.0
    for p in primes_upto(N):
        k = 1
        while p ** k <= N:
            n = p ** k
            lf = log(n)
            s += (log(p) / sqrt(n)) * (hat_f(lf, T) + hat_f(-lf, T))
            k += 1
    return s

def balance(T, N=5000):
    return -(prime_power_sum(T, N=N) - archimedean_term(T))

def test():
    Ts = np.arange(2.40, 2.5001, 0.01)
    last_T = None
    last_val = None
    for T in Ts:
        val = balance(float(T))
        print("T=", float(T), "LHS-RHS=", val)
        if last_val is not None and last_val > 0 and val < 0:
            print("sign_change_interval", (last_T, float(T)))
        last_T = float(T)
        last_val = val

if __name__ == "__main__":
    test()
