import numpy as np
from math import log, sqrt

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

def prime_power_sum_interval(T, N0, N1):
    s = 0.0
    for p in primes_upto(N1):
        k = 1
        while p ** k <= N1:
            n = p ** k
            if n > N0:
                lf = log(n)
                s += (log(p) / sqrt(n)) * (hat_f(lf, T) + hat_f(-lf, T))
            k += 1
    return s

def test():
    for T in [2.44, 2.445, 2.45]:
        print("T =", T)
        last = None
        for N in [200, 500, 1000, 2000, 5000, 10000]:
            val = prime_power_sum_interval(T, 0, N)
            print("N =", N, "partial_sum =", val)
            if last is not None:
                print("tail_from_prev =", val - last)
            last = val
        print()

if __name__ == "__main__":
    test()
