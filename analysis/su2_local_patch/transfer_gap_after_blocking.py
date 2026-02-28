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

def time_transfer_matrix(U, L, kappa=1.0):
    """
    Build transfer matrix proxy T acting between spatial slices.
    States labeled by spatial site index.
    """
    Ns = L**3
    T = np.zeros((Ns,Ns), dtype=np.float64)

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s4 = idx(x,y,z,t,L)
                    sp4 = idx(x,y,z,(t+1)%L,L)
                    s3 = x*L*L + y*L + z
                    tr = np.trace(U[s4,3]).real
                    w = float(np.exp(kappa * tr))
                    T[s3,s3] += w

    # Normalize by time extent
    T /= L
    return T

def transfer_gap(T):
    vals = np.linalg.eigvalsh(T)
    vals = np.sort(vals)[::-1]
    if len(vals) < 2:
        return 0.0
    return float(vals[0] - vals[1])

def main():
    L = 8
    b = 2
    beta = 2.3
    sweeps = 8
    eps = 0.25
    kappa = 1.0

    U = make_random_U(L,0)
    U,_ = thermalize_metropolis(U,L,beta,sweeps=sweeps,eps=eps,seed=1)

    T0 = time_transfer_matrix(U,L,kappa)
    gap0 = transfer_gap(T0)

    U1 = block_weighted_covariant_4d(U,L,b,beta,alpha_override=0.0)
    T1 = time_transfer_matrix(U1,L//b,kappa)
    gap1 = transfer_gap(T1)

    print("transfer_gap_fine", gap0)
    print("transfer_gap_coarse", gap1)
    print("ratio", gap1/gap0 if gap0>0 else np.nan)

if __name__ == "__main__":
    main()
