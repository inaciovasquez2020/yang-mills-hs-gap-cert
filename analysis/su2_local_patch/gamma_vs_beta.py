import numpy as np
from analysis.su2_local_patch.laplacian_gap_after_blocking import (
    make_random_U, thermalize_metropolis,
    build_W_from_links, laplacian_gap
)
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d

def gamma_for(beta, L=12, b=2, sweeps=6, eps=0.25, kappa=1.0, seed=1):
    U = make_random_U(L,0)
    U,_ = thermalize_metropolis(U,L,beta,sweeps=sweeps,eps=eps,seed=seed)

    gapL = laplacian_gap(build_W_from_links(U,L,kappa))
    Uc = block_weighted_covariant_4d(U,L,b,beta,alpha_override=0.0)
    gapLb = laplacian_gap(build_W_from_links(Uc,L//b,kappa))

    return (np.log(gapLb) - np.log(gapL)) / np.log(b), gapL, gapLb

def main():
    L = 12
    b = 2
    sweeps = 6
    eps = 0.25
    kappa = 1.0
    betas = [1.6, 2.0, 2.3, 2.6, 3.0]

    print("L b sweeps eps kappa")
    print(L, b, sweeps, eps, kappa)
    print("beta gamma gapL gapLb")

    for beta in betas:
        g, gapL, gapLb = gamma_for(beta, L=L, b=b, sweeps=sweeps, eps=eps, kappa=kappa, seed=1)
        print(beta, g, gapL, gapLb)

if __name__ == "__main__":
    main()
