import numpy as np

def su2_from_quat(a0,a1,a2,a3):
    return np.array([[a0+1j*a3, a2+1j*a1],
                     [-a2+1j*a1, a0-1j*a3]], dtype=np.complex128)

def su2_random(rng):
    v = rng.normal(size=4)
    v /= np.linalg.norm(v)
    return su2_from_quat(v[0],v[1],v[2],v[3])

def su2_near_identity(rng, eps):
    v = rng.normal(size=3)
    n = np.linalg.norm(v)
    if n < 1e-12:
        a = np.array([0.0,0.0,0.0])
    else:
        a = (v/n) * (eps * rng.uniform(0.0,1.0))
    a0 = np.sqrt(max(0.0, 1.0 - np.dot(a,a)))
    return su2_from_quat(a0,a[0],a[1],a[2])

def dagger(U):
    return U.conj().T

def matmul(A,B):
    return A @ B

def re_tr(U):
    return float(np.real(np.trace(U)))

def idx(x,y,z,t,L):
    return (((x%L)*L + (y%L))*L + (z%L))*L + (t%L)

def shift(coord, mu, s, L):
    x,y,z,t = coord
    if mu==0: x = (x + s) % L
    if mu==1: y = (y + s) % L
    if mu==2: z = (z + s) % L
    if mu==3: t = (t + s) % L
    return (x,y,z,t)

def staple(U, coord, mu, L):
    V = np.zeros((2,2), dtype=np.complex128)
    for nu in range(4):
        if nu == mu:
            continue
        c = coord
        c_mu_p = shift(c, mu, +1, L)
        c_nu_p = shift(c, nu, +1, L)
        c_nu_m = shift(c, nu, -1, L)
        c_nu_m_mu_p = shift(c_nu_m, mu, +1, L)

        U_nu_c = U[idx(*c,L), nu]
        U_mu_c_nu_p = U[idx(*c_nu_p,L), mu]
        U_nu_c_mu_p = U[idx(*c_mu_p,L), nu]
        V += matmul(U_nu_c, matmul(U_mu_c_nu_p, dagger(U_nu_c_mu_p)))

        U_nu_c_nu_m = U[idx(*c_nu_m,L), nu]
        U_mu_c_nu_m = U[idx(*c_nu_m,L), mu]
        U_nu_c_nu_m_mu_p = U[idx(*c_nu_m_mu_p,L), nu]
        V += matmul(dagger(U_nu_c_nu_m), matmul(U_mu_c_nu_m, U_nu_c_nu_m_mu_p))
    return V

def metropolis_sweep(U, beta, eps, rng, L):
    N = L**4
    acc = 0
    tot = 0
    for s in range(N):
        x = s // (L*L*L)
        r = s - x*(L*L*L)
        y = r // (L*L)
        r = r - y*(L*L)
        z = r // L
        t = r - z*L
        coord = (x,y,z,t)
        for mu in range(4):
            V = staple(U, coord, mu, L)
            Uold = U[idx(*coord,L), mu]
            R = su2_near_identity(rng, eps)
            Unew = matmul(R, Uold)

            sold = -0.5 * beta * re_tr(matmul(Uold, V))
            snew = -0.5 * beta * re_tr(matmul(Unew, V))
            dS = snew - sold

            if dS <= 0.0 or rng.uniform() < np.exp(-dS):
                U[idx(*coord,L), mu] = Unew
                acc += 1
            tot += 1
    return acc / max(1,tot)

def polyakov_loops(U, L, mu_t=3):
    P = np.zeros((L,L,L), dtype=np.complex128)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                M = np.eye(2, dtype=np.complex128)
                for t in range(L):
                    M = matmul(M, U[idx(x,y,z,t,L), mu_t])
                P[x,y,z] = np.trace(M) / 2.0
    return P

def corr_polyakov(P, L):
    C = np.zeros(L//2 + 1, dtype=np.float64)
    norm = 0
    for r in range(L//2 + 1):
        s = 0.0
        cnt = 0
        for x in range(L):
            for y in range(L):
                for z in range(L):
                    v1 = P[x,y,z]
                    v2 = P[(x+r)%L,y,z]
                    s += np.real(v1 * np.conj(v2))
                    cnt += 1
        C[r] = s / cnt
        norm += 1
    return C

def effective_mass(C):
    m = []
    for r in range(len(C)-1):
        if C[r+1] <= 0 or C[r] <= 0:
            m.append(np.nan)
        else:
            m.append(np.log(C[r]/C[r+1]))
    return np.array(m, dtype=np.float64)

def run(L=6, beta=1.0, sweeps=300, therm=100, eps=0.25, seed=0):
    rng = np.random.default_rng(seed)
    U = np.empty((L**4,4,2,2), dtype=np.complex128)
    for s in range(L**4):
        for mu in range(4):
            U[s,mu] = su2_random(rng)

    acc_hist = []
    C_acc = None
    n_meas = 0

    for it in range(sweeps):
        acc = metropolis_sweep(U, beta, eps, rng, L)
        acc_hist.append(acc)
        if it >= therm:
            P = polyakov_loops(U, L, mu_t=3)
            C = corr_polyakov(P, L)
            if C_acc is None:
                C_acc = C.copy()
            else:
                C_acc += C
            n_meas += 1

    C_mean = C_acc / max(1,n_meas)
    m_eff = effective_mass(C_mean)

    print("L beta sweeps therm eps seed")
    print(L, beta, sweeps, therm, eps, seed)
    print("accept_mean", float(np.mean(acc_hist)))
    print("C_r", " ".join(f"{v:.6e}" for v in C_mean))
    print("m_eff_r", " ".join("nan" if np.isnan(v) else f"{v:.6f}" for v in m_eff))

if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument("--L", type=int, default=6)
    ap.add_argument("--beta", type=float, default=1.0)
    ap.add_argument("--sweeps", type=int, default=300)
    ap.add_argument("--therm", type=int, default=100)
    ap.add_argument("--eps", type=float, default=0.25)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    run(L=args.L, beta=args.beta, sweeps=args.sweeps, therm=args.therm, eps=args.eps, seed=args.seed)
