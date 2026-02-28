import argparse
import numpy as np
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d
from analysis.su2_local_patch.metropolis_su2_4d import idx, random_su2, thermalize_metropolis

def make_random_U(L, seed):
    rng = np.random.default_rng(seed)
    U = np.zeros((L**4,4,2,2), dtype=np.complex128)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s = idx(x,y,z,t,L)
                    for mu in range(4):
                        U[s,mu] = random_su2(rng)
    return U

def shift4(x,y,z,t,mu,step,L):
    if mu==0: return ((x+step)%L,y,z,t)
    if mu==1: return (x,(y+step)%L,z,t)
    if mu==2: return (x,y,(z+step)%L,t)
    if mu==3: return (x,y,z,(t+step)%L)
    raise ValueError("mu")

def build_W_from_links(U, L, kappa=1.0):
    N = L**4
    W = np.zeros((N,N), dtype=np.float64)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s = idx(x,y,z,t,L)
                    for mu in range(4):
                        xp,yp,zp,tp = shift4(x,y,z,t,mu,+1,L)
                        sp = idx(xp,yp,zp,tp,L)
                        tr = np.trace(U[s,mu]).real
                        w = float(np.exp(kappa * tr))
                        W[s,sp] = w
                        W[sp,s] = w
    return W

def normalized_laplacian(W, eps=1e-12):
    d = np.sum(W, axis=1)
    inv_sqrt = 1.0 / np.sqrt(np.maximum(d, eps))
    Dinv = np.diag(inv_sqrt)
    L = np.eye(W.shape[0]) - Dinv @ W @ Dinv
    return L

def laplacian_gap(W):
    L = normalized_laplacian(W)
    vals = np.linalg.eigvalsh(L)
    vals = np.sort(vals)
    return float(vals[1])

def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("--lattice", type=int, default=8)
    p.add_argument("--blocking", type=int, default=2)
    p.add_argument("--beta", type=float, default=2.3)
    p.add_argument("--sweeps", type=int, default=10)
    p.add_argument("--eps", type=float, default=0.25)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--therm-seed", type=int, default=1)
    p.add_argument("--kappa", type=float, default=1.0)
    p.add_argument("--scale-correct", action="store_true")
    return p.parse_args()

def main():
    args = parse_args()

    L = args.lattice
    b = args.blocking
    beta = args.beta
    sweeps = args.sweeps
    eps = args.eps
    kappa = args.kappa

    if L % b != 0:
        raise SystemExit("L must be divisible by b")

    U = make_random_U(L, args.seed)
    U, acc = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=args.therm_seed)

    Wf = build_W_from_links(U, L, kappa=kappa)
    gap_f = laplacian_gap(Wf)

    Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=0.0)
    Wc = build_W_from_links(Uc, L//b, kappa=kappa)
    gap_c = laplacian_gap(Wc)

    print("accept", acc)
    print("fine_gap", gap_f)
    print("coarse_gap", gap_c)
    print("ratio", gap_c/gap_f if gap_f!=0 else np.nan)

    if args.scale_correct:
        print("scale_corrected", gap_c / (b**2 * gap_f))

if __name__ == "__main__":
    main()
