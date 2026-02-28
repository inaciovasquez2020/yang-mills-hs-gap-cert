import argparse
import numpy as np
from analysis.su2_local_patch.laplacian_gap_after_blocking import (
    make_random_U, build_W_from_links, laplacian_gap
)
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d
from analysis.su2_local_patch.metropolis_su2_4d import thermalize_metropolis

def parse_args():
    p = argparse.ArgumentParser()
    p.add_argument("--lattice", type=int, default=8)
    p.add_argument("--blocking", type=int, default=2)
    p.add_argument("--beta", type=float, default=2.3)
    p.add_argument("--sweeps", type=int, default=0)
    p.add_argument("--eps", type=float, default=0.25)
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--therm-seed", type=int, default=1)
    p.add_argument("--kappa", type=float, default=1.0)
    return p.parse_args()

def main():
    args = parse_args()
    L = args.lattice
    b = args.blocking
    if L % b != 0:
        raise SystemExit("L must be divisible by b")

    U = make_random_U(L, args.seed)
    if args.sweeps > 0:
        U, _ = thermalize_metropolis(
            U, L, args.beta,
            sweeps=args.sweeps,
            eps=args.eps,
            seed=args.therm_seed
        )

    Wf = build_W_from_links(U, L, kappa=args.kappa)
    gap_f = laplacian_gap(Wf)

    Uc = block_weighted_covariant_4d(U, L, b, args.beta, alpha_override=0.0)
    Wc = build_W_from_links(Uc, L//b, kappa=args.kappa)
    gap_c = laplacian_gap(Wc)

    gamma = (np.log(gap_c) - np.log(gap_f)) / np.log(b)

    print("fine_gap", gap_f)
    print("coarse_gap", gap_c)
    print("gamma", float(gamma))

if __name__ == "__main__":
    main()
