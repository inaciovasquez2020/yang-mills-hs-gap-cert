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
    # smallest eigenvalue ~0; return second smallest
    return float(vals[1])

def main():
    L = 8
    b = 2
    beta = 2.3
    sweeps = 10
    eps = 0.25
    kappa = 1.0

    U = make_random_U(L, 0)
    U, acc = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=1)

    Wf = build_W_from_links(U, L, kappa=kappa)
    gap_f = laplacian_gap(Wf)

    Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=0.0)
    Wc = build_W_from_links(Uc, L//b, kappa=kappa)
    gap_c = laplacian_gap(Wc)

    print("accept", acc)
    print("fine_gap", gap_f)
    print("coarse_gap", gap_c)
    print("ratio", gap_c/gap_f if gap_f != 0 else np.nan)

if __name__ == "__main__":
    main()
