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

def plaquette(U, coord, mu, nu, L):
    c = coord
    c_mu = shift(c, mu, +1, L)
    c_nu = shift(c, nu, +1, L)

    U1 = U[idx(*c,L), mu]
    U2 = U[idx(*c_mu,L), nu]
    U3 = dagger(U[idx(*c_nu,L), mu])
    U4 = dagger(U[idx(*c,L), nu])

    return re_tr(U1 @ U2 @ U3 @ U4) / 2.0

def metropolis_sweep(U, beta, eps, rng, L):
    N = L**4
    for s in range(N):
        x = s // (L*L*L)
        r = s - x*(L*L*L)
        y = r // (L*L)
        r -= y*(L*L)
        z = r // L
        t = r - z*L
        coord = (x,y,z,t)

        for mu in range(4):
            Uold = U[idx(*coord,L), mu]
            R = su2_near_identity(rng, eps)
            Unew = R @ Uold

            delta = 0.0
            for nu in range(4):
                if nu == mu:
                    continue

                p_old = plaquette(U, coord, mu, nu, L)

                U[idx(*coord,L), mu] = Unew
                p_new = plaquette(U, coord, mu, nu, L)
                U[idx(*coord,L), mu] = Uold

                delta += p_new - p_old

            dS = -beta * delta

            if dS <= 0.0 or rng.uniform() < np.exp(-dS):
                U[idx(*coord,L), mu] = Unew

def measure_glueball_connected(U, L):
    Pvals = []

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    c = (x,y,z,t)
                    Pvals.append(plaquette(U, c, 0, 1, L))

    Pvals = np.array(Pvals)
    meanP = np.mean(Pvals)

    G = np.zeros(L)
    count = np.zeros(L)

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    c = (x,y,z,t)
                    val1 = plaquette(U, c, 0, 1, L) - meanP

                    for dx in range(L):
                        c2 = ((x+dx)%L,y,z,t)
                        val2 = plaquette(U, c2, 0, 1, L) - meanP
                        G[dx] += val1 * val2
                        count[dx] += 1

    return G / count

def effective_mass(C):
    m = []
    for r in range(len(C)-1):
        if C[r+1] <= 0 or C[r] <= 0:
            m.append(np.nan)
        else:
            m.append(np.log(C[r]/C[r+1]))
    return np.array(m)

def run(L=6, beta=0.8, sweeps=3000, therm=800, eps=0.8, seed=0):
    rng = np.random.default_rng(seed)
    U = np.empty((L**4,4,2,2), dtype=np.complex128)

    for s in range(L**4):
        for mu in range(4):
            U[s,mu] = su2_random(rng)

    for i in range(sweeps):
        metropolis_sweep(U, beta, eps, rng, L)

    C = measure_glueball_connected(U, L)
    m = effective_mass(C)

    print("Connected glueball correlator:")
    print("C_r", " ".join(f"{v:.6e}" for v in C[:6]))
    print("m_eff", " ".join("nan" if np.isnan(v) else f"{v:.6f}" for v in m[:5]))

if __name__ == "__main__":
    run()
