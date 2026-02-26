import itertools
import math
from collections import defaultdict

def log2(x):
    return math.log(x, 2.0)

class FiniteGroup:
    def __init__(self, elems, mul, inv, conj_class_key, chi2):
        self.elems = elems
        self.mul = mul
        self.inv = inv
        self.conj_class_key = conj_class_key
        self.chi2 = chi2

def group_Z2():
    elems = [0,1]
    def mul(a,b): return a^b
    def inv(a): return a
    def ckey(a): return a
    def chi2(a): return 1 if a==0 else -1
    return FiniteGroup(elems,mul,inv,ckey,chi2)

def group_S3():
    elems = list(range(6))
    e = 0
    a = 1
    b = 2
    a2 = 3
    ab = 4
    a2b = 5
    def mul(x,y):
        table = [
            [e, a, b, a2, ab, a2b],
            [a, a2, ab, e, a2b, b],
            [b, a2b, e, ab, a, a2],
            [a2, e, a2b, a, b, ab],
            [ab, b, a, a2b, a2, e],
            [a2b, ab, a2, b, e, a],
        ]
        return table[x][y]
    def inv(x):
        invs = [e, a2, b, a, a2b, ab]
        return invs[x]
    def ckey(x):
        if x==e: return "e"
        if x in (b,ab,a2b): return "t"
        return "c"
    def chi2(x):
        k = ckey(x)
        if k=="e": return 2
        if k=="t": return 0
        return -1
    return FiniteGroup(elems,mul,inv,ckey,chi2)

def plaquette(g, U, p):
    a,b,c,d = p
    return g.mul(g.mul(g.mul(U[a], U[b]), g.inv(U[c])), g.inv(U[d]))

def cmi_from_counts(count_xyz, count_xbz, count_ybz, count_bz, total):
    I = 0.0
    for (x,y,b), w in count_xyz.items():
        pxyz = w / total
        px_b = count_xbz[(x,b)] / total
        py_b = count_ybz[(y,b)] / total
        pb = count_bz[b] / total
        if pxyz <= 0 or px_b<=0 or py_b<=0 or pb<=0:
            continue
        I += pxyz * log2((pxyz * pb) / (px_b * py_b))
    return I

def exact_cmi_toy(g, beta, lattice="2x2"):
    if lattice != "2x2":
        raise ValueError("only 2x2 implemented")

    links = ["t0_x0", "t0_x1", "t1_x0", "t1_x1", "x0_v", "x1_v"]
    idx = {name:i for i,name in enumerate(links)}

    P_past = [("t0_x0","x0_v","t0_x1","x1_v")]
    P_fut  = [("t1_x0","x0_v","t1_x1","x1_v")]
    P_bdry = [("t0_x0","t1_x0","t0_x1","t1_x1")]

    P_past_i = [(idx[a],idx[b],idx[c],idx[d]) for (a,b,c,d) in P_past]
    P_fut_i  = [(idx[a],idx[b],idx[c],idx[d]) for (a,b,c,d) in P_fut]
    P_bdry_i = [(idx[a],idx[b],idx[c],idx[d]) for (a,b,c,d) in P_bdry]

    count_xyz = defaultdict(float)
    count_xbz = defaultdict(float)
    count_ybz = defaultdict(float)
    count_bz  = defaultdict(float)

    total = 0.0

    for assigns in itertools.product(g.elems, repeat=len(links)):
        U = assigns

        w = 1.0
        for p in (P_past_i + P_fut_i + P_bdry_i):
            gp = plaquette(g, U, p)
            w *= math.exp(beta * g.chi2(gp))
        if w == 0.0:
            continue

        x = tuple(g.conj_class_key(plaquette(g,U,p)) for p in P_past_i)
        y = tuple(g.conj_class_key(plaquette(g,U,p)) for p in P_fut_i)
        b = tuple(g.conj_class_key(plaquette(g,U,p)) for p in P_bdry_i)

        count_xyz[(x,y,b)] += w
        count_xbz[(x,b)] += w
        count_ybz[(y,b)] += w
        count_bz[b] += w
        total += w

    I = cmi_from_counts(count_xyz, count_xbz, count_ybz, count_bz, total)
    return I

def sweep():
    for name, grp in [("Z2", group_Z2()), ("S3", group_S3())]:
        print(f"\nGROUP={name}")
        for beta in [0.0, 0.2, 0.5, 1.0, 2.0]:
            I = exact_cmi_toy(grp, beta)
            print(f"beta={beta:.2f}  I(P;F|B)={I:.8f} bits")

if __name__ == "__main__":
    sweep()
