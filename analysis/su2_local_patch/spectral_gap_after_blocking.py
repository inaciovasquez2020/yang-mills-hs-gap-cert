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
    H = np.zeros((N,N))
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
                    H[s,s] += val
    return H

def smallest_gap(H):
    w = np.linalg.eigvalsh(H)
    w = np.sort(w)
    return float(w[1] - w[0])

def main():
    L = 6
    b = 3
    beta = 2.3
    sweeps = 10
    eps = 0.25

    U = make_random_U(L, 0)
    U, _ = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=100)

    H_fine = plaquette_operator(U, L)
    gap_fine = smallest_gap(H_fine)

    Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=0.0)
    H_coarse = plaquette_operator(Uc, L//b)
    gap_coarse = smallest_gap(H_coarse)

    print("Fine gap:", gap_fine)
    print("Coarse gap:", gap_coarse)
    print("Gap ratio (coarse/fine):", gap_coarse / gap_fine if gap_fine != 0 else np.nan)

if __name__ == "__main__":
    main()
