import random
from ym.vortex_mixing.python.su2 import haar_su2, mul, trace

def sample_trace_neg(M,n=10000,seed=0):
    rng=random.Random(seed)
    vals=[]
    for _ in range(n):
        g=haar_su2(rng)
        for __ in range(M-1):
            g=mul(haar_su2(rng),g)
        vals.append(trace(g))
    return sum(1 for v in vals if v<0)/len(vals)

def main():
    Ms=[1,2,4,8,16,32,64]
    for M in Ms:
        pneg=sample_trace_neg(M,n=20000)
        print(f"M={M}, P(trace<0)={pneg:.4f}, dev={abs(pneg-0.5):.4f}")

if __name__=="__main__":
    main()
