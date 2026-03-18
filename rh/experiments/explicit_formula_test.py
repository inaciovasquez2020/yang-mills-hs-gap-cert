import numpy as np
from math import exp, log, pi, sqrt

def primes_upto(N):
    sieve = [True]*(N+1)
    sieve[0]=sieve[1]=False
    for i in range(2,int(N**0.5)+1):
        if sieve[i]:
            for j in range(i*i,N+1,i):
                sieve[j]=False
    return [i for i in range(2,N+1) if sieve[i]]

def von_mangoldt(n):
    for p in range(2,int(n**0.5)+1):
        if n%p==0:
            m=n
            while m%p==0:
                m//=p
            return log(p) if m==1 else 0.0
    return log(n)

def f_hat(t, a):
    return np.sqrt(np.pi/a)*np.exp(-t*t/(4*a))

def explicit_formula(a, N=1000):
    primes = primes_upto(N)
    lhs = f_hat(0,a)*log(pi)
    rhs = 0.0
    for p in primes:
        k = 1
        while p**k <= N:
            n = p**k
            rhs += (log(p)/sqrt(n))*(f_hat(log(n),a)+f_hat(-log(n),a))
            k += 1
    return lhs, rhs

def test():
    for a in [0.1,0.5,1.0,2.0]:
        lhs, rhs = explicit_formula(a)
        print("a=",a,"LHS=",lhs,"RHS=",rhs,"LHS-RHS=",lhs-rhs)

if __name__ == "__main__":
    test()
