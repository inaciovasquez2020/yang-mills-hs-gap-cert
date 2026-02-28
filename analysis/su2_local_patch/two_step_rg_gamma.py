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

def gamma(g_f, g_c, b):
    return (np.log(g_c) - np.log(g_f)) / np.log(b)

def main():
    args = parse_args()
    L = args.lattice
    b = args.blocking
    if L % b != 0 or (L // b) % b != 0:
        raise SystemExit("L must be divisible by b^2 for two-step test")

    # initial field
    U = make_random_U(L, args.seed)
    if args.sweeps > 0:
        U, _ = thermalize_metropolis(
            U, L, args.beta,
            sweeps=args.sweeps,
            eps=args.eps,
            seed=args.therm_seed
        )

    # fine
    W0 = build_W_from_links(U, L, kappa=args.kappa)
    g0 = laplacian_gap(W0)

    # first block
    U1 = block_weighted_covariant_4d(U, L, b, args.beta, alpha_override=0.0)
    W1 = build_W_from_links(U1, L//b, kappa=args.kappa)
    g1 = laplacian_gap(W1)

    # second block
    U2 = block_weighted_covariant_4d(U1, L//b, b, args.beta, alpha_override=0.0)
    W2 = build_W_from_links(U2, L//(b*b), kappa=args.kappa)
    g2 = laplacian_gap(W2)

    gamma1 = gamma(g0, g1, b)
    gamma2 = gamma(g1, g2, b)

    print("g0", g0)
    print("g1", g1)
    print("g2", g2)
    print("gamma_step1", float(gamma1))
    print("gamma_step2", float(gamma2))

if __name__ == "__main__":
    main()
