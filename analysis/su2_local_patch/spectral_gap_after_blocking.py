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

def plaquette_operator(U, L):
    N = L**4
    H = np.zeros((N,N), dtype=np.float64)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s = idx(x,y,z,t,L)
                    xp = idx((x+1)%L,y,z,t,L)
                    yp = idx(x,(y+1)%L,z,t,L)
                    val = np.trace(
                        U[s,0] @ U[xp,1] @
                        np.linalg.inv(U[yp,0]) @
                        np.linalg.inv(U[s,1])
                    ).real
                    H[s,s] += float(val)
    return H

def smallest_gap(H):
    w = np.linalg.eigvalsh(H)
    w = np.sort(w)
    if w.shape[0] < 2:
        return 0.0
    return float(w[1] - w[0])

def parse_args():
    p = argparse.ArgumentParser(description="Spectral gap proxy before/after blocking (plaquette-diagonal operator).")
    p.add_argument("--lattice", type=int, default=6, help="Fine lattice size L (must be divisible by blocking).")
    p.add_argument("--blocking", type=int, default=3, help="Blocking factor b.")
    p.add_argument("--beta", type=float, default=2.3, help="Inverse coupling beta.")
    p.add_argument("--sweeps", type=int, default=10, help="Metropolis sweeps for thermalization.")
    p.add_argument("--eps", type=float, default=0.25, help="Metropolis proposal step size.")
    p.add_argument("--seed", type=int, default=0, help="Seed for initial random field.")
    p.add_argument("--therm-seed", type=int, default=100, help="Seed for Metropolis thermalization.")
    p.add_argument("--alpha", type=float, default=0.0, help="alpha_override for blocking kernel.")
    p.add_argument("--scale-correct", action="store_true", help="Also print coarse/(b^2 * fine).")
    return p.parse_args()

def main():
    args = parse_args()
    L = int(args.lattice)
    b = int(args.blocking)
    if L % b != 0:
        raise SystemExit(f"L={L} must be divisible by b={b}")
    beta = float(args.beta)
    sweeps = int(args.sweeps)
    eps = float(args.eps)

    U = make_random_U(L, args.seed)
    U, acc = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=args.therm_seed)

    H_fine = plaquette_operator(U, L)
    gap_fine = smallest_gap(H_fine)

    Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=float(args.alpha))
    H_coarse = plaquette_operator(Uc, L//b)
    gap_coarse = smallest_gap(H_coarse)

    print("accept_mean", float(acc))
    print("Fine gap:", gap_fine)
    print("Coarse gap:", gap_coarse)
    ratio = (gap_coarse / gap_fine) if gap_fine != 0 else np.nan
    print("Gap ratio (coarse/fine):", ratio)

    if args.scale_correct:
        corr = (gap_coarse / ((b**2) * gap_fine)) if gap_fine != 0 else np.nan
        print("Scale-corrected ratio (coarse / (b^2 * fine)):", corr)

if __name__ == "__main__":
    main()
