import numpy as np

def idx(x,y,z,t,L):
    return ((x*L + y)*L + z)*L + t

def random_su2(rng):
    a = rng.normal(size=4)
    a = a / np.linalg.norm(a)
    a0,a1,a2,a3 = a
    return np.array([
        [a0+1j*a3,  a2+1j*a1],
        [-a2+1j*a1, a0-1j*a3]
    ], dtype=np.complex128)

def su2_inv(U):
    return U.conj().T

def shift4(x,y,z,t,mu,step,L):
    if mu==0: return ((x+step)%L,y,z,t)
    if mu==1: return (x,(y+step)%L,z,t)
    if mu==2: return (x,y,(z+step)%L,t)
    if mu==3: return (x,y,z,(t+step)%L)
    raise ValueError("mu")

def staple(U, L, x,y,z,t, mu):
    S = np.zeros((2,2), dtype=np.complex128)
    for nu in range(4):
        if nu == mu:
            continue

        # forward staple: U_nu(x) U_mu(x+nu) U_nu(x+mu)^\dagger
        s0 = idx(x,y,z,t,L)
        xn,yn,zn,tn = shift4(x,y,z,t,nu,+1,L)
        xm,ym,zm,tm = shift4(x,y,z,t,mu,+1,L)
        s_n  = idx(xn,yn,zn,tn,L)
        s_m  = idx(xm,ym,zm,tm,L)
        xnm,ynm,znm,tnm = shift4(xn,yn,zn,tn,mu,+1,L)
        s_nm = idx(xnm,ynm,znm,tnm,L)

        S += U[s0,nu] @ U[s_n,mu] @ su2_inv(U[s_m,nu])

        # backward staple: U_nu^\dagger(x-nu) U_mu(x-nu) U_nu(x-nu+mu)
        xb,yb,zb,tb = shift4(x,y,z,t,nu,-1,L)
        s_b = idx(xb,yb,zb,tb,L)
        xbm,ybm,zbm,tbm = shift4(xb,yb,zb,tb,mu,+1,L)
        s_bm = idx(xbm,ybm,zbm,tbm,L)

        S += su2_inv(U[s_b,nu]) @ U[s_b,mu] @ U[s_bm,nu]

    return S

def local_action_term(U_mu, S, beta):
    # Wilson local contribution: - (beta/2) Re Tr(U_mu S)
    return -0.5 * beta * np.trace(U_mu @ S).real

def propose_su2(rng, eps):
    # small random SU(2) rotation around identity
    v = rng.normal(size=3)
    n = np.linalg.norm(v)
    if n == 0:
        return np.eye(2, dtype=np.complex128)
    v = v / n
    theta = eps * rng.normal()
    c = np.cos(theta)
    s = np.sin(theta)
    vx,vy,vz = v
    # exp(i theta v·sigma) = c I + i s (v·sigma)
    return np.array([[c+1j*s*vz, 1j*s*(vx-1j*vy)],
                     [1j*s*(vx+1j*vy), c-1j*s*vz]], dtype=np.complex128)

def thermalize_metropolis(U, L, beta, sweeps=10, eps=0.25, seed=0):
    rng = np.random.default_rng(seed)
    acc = 0
    tot = 0

    for _ in range(sweeps):
        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for t in range(L):
                        s0 = idx(x,y,z,t,L)
                        for mu in range(4):
                            S = staple(U, L, x,y,z,t, mu)
                            Uold = U[s0,mu]
                            Sold = local_action_term(Uold, S, beta)

                            R = propose_su2(rng, eps)
                            Unew = R @ Uold
                            Snew = local_action_term(Unew, S, beta)

                            dS = Snew - Sold
                            if dS <= 0 or rng.random() < np.exp(-dS):
                                U[s0,mu] = Unew
                                acc += 1
                            tot += 1

    return U, (acc / tot if tot else 0.0)
