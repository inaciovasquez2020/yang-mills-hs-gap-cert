import numpy as np
from analysis.su2_local_patch.metropolis_su2_4d import idx, random_su2, thermalize_metropolis

def plaquette_xy_at_t(U, L, x, y, z, t, mu=0, nu=1):
    s  = idx(x,y,z,t,L)
    if mu==0:
        s_mu = idx((x+1)%L,y,z,t,L)
    elif mu==1:
        s_mu = idx(x,(y+1)%L,z,t,L)
    elif mu==2:
        s_mu = idx(x,y,(z+1)%L,t,L)
    else:
        s_mu = idx(x,y,z,(t+1)%L,L)

    if nu==0:
        s_nu = idx((x+1)%L,y,z,t,L)
    elif nu==1:
        s_nu = idx(x,(y+1)%L,z,t,L)
    elif nu==2:
        s_nu = idx(x,y,(z+1)%L,t,L)
    else:
        s_nu = idx(x,y,z,(t+1)%L,L)

    if mu==0 and nu==1:
        s_munu = idx((x+1)%L,(y+1)%L,z,t,L)
    elif mu==0 and nu==2:
        s_munu = idx((x+1)%L,y,(z+1)%L,t,L)
    elif mu==1 and nu==2:
        s_munu = idx(x,(y+1)%L,(z+1)%L,t,L)
    else:
        # minimal fallback for other pairs
        xm = (x + (1 if mu==0 else 0)) % L
        ym = (y + (1 if mu==1 else 0)) % L
        zm = (z + (1 if mu==2 else 0)) % L
        tm = (t + (1 if mu==3 else 0)) % L
        xn = (x + (1 if nu==0 else 0)) % L
        yn = (y + (1 if nu==1 else 0)) % L
        zn = (z + (1 if nu==2 else 0)) % L
        tn = (t + (1 if nu==3 else 0)) % L
        s_munu = idx((xm + (1 if nu==0 else 0)) % L,
                     (ym + (1 if nu==1 else 0)) % L,
                     (zm + (1 if nu==2 else 0)) % L,
                     (tm + (1 if nu==3 else 0)) % L, L)

    U_mu = U[s,mu]
    U_nu = U[s_mu,nu]
    U_mu_dag = np.linalg.inv(U[s_nu,mu])
    U_nu_dag = np.linalg.inv(U[s,nu])
    return np.trace(U_mu @ U_nu @ U_mu_dag @ U_nu_dag).real

def slice_plaquette_avg(U, L, t, mu=0, nu=1):
    total = 0.0
    count = 0
    for x in range(L):
        for y in range(L):
            for z in range(L):
                total += plaquette_xy_at_t(U,L,x,y,z,t,mu=mu,nu=nu)
                count += 1
    return total / count

def correlator_G(U, L, max_tau=4, mu=0, nu=1):
    P = np.array([slice_plaquette_avg(U,L,t,mu=mu,nu=nu) for t in range(L)], dtype=np.float64)
    # time-translation averaged correlator
    G = []
    for tau in range(max_tau+1):
        Gtau = 0.0
        for t in range(L):
            Gtau += P[t] * P[(t+tau)%L]
        Gtau /= L
        G.append(Gtau)
    return np.array(G, dtype=np.float64)

def effective_mass(G):
    # m_eff(tau) = log(G(tau)/G(tau+1))
    meff = []
    for tau in range(len(G)-1):
        if G[tau+1] <= 0 or G[tau] <= 0:
            meff.append(np.nan)
        else:
            meff.append(float(np.log(G[tau]/G[tau+1])))
    return np.array(meff, dtype=np.float64)

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

def main():
    L = 8
    beta = 2.3
    sweeps = 20
    eps = 0.25
    seed = 1

    U = make_random_U(L,0)
    U, acc = thermalize_metropolis(U,L,beta,sweeps=sweeps,eps=eps,seed=seed)

    G = correlator_G(U,L,max_tau=min(4, L-2), mu=0, nu=1)
    meff = effective_mass(G)

    print("accept", acc)
    print("G", " ".join([f"{x:.6g}" for x in G]))
    print("m_eff", " ".join([("nan" if np.isnan(x) else f"{x:.6g}") for x in meff]))

if __name__ == "__main__":
    main()
