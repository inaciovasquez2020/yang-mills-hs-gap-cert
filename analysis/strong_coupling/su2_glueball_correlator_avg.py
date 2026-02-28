import numpy as np
import time
import argparse

# ============================================================
# Basic SU(2) utilities
# ============================================================

def su2_random(rng):
    v = rng.normal(size=4)
    v /= np.linalg.norm(v)
    a0, a1, a2, a3 = v
    return np.array([
        [a0 + 1j*a3,  a2 + 1j*a1],
        [-a2 + 1j*a1, a0 - 1j*a3]
    ], dtype=np.complex128)

def dag(U):
    return U.conj().T

def project_to_su2(M):
    H = M.conj().T @ M
    w, V = np.linalg.eigh(H)
    H_inv_sqrt = V @ np.diag(1.0 / np.sqrt(w + 1e-12)) @ dag(V)
    U = M @ H_inv_sqrt
    return U

# ============================================================
# Lattice helpers
# ============================================================

def neighbors(x, mu, L):
    xp = list(x)
    xm = list(x)
    xp[mu] = (xp[mu] + 1) % L
    xm[mu] = (xm[mu] - 1) % L
    return tuple(xp), tuple(xm)

def staple(U, x, mu, L):
    S = np.zeros((2,2), dtype=np.complex128)
    for nu in range(4):
        if nu == mu:
            continue

        xp_mu, _ = neighbors(x, mu, L)
        xp_nu, xm_nu = neighbors(x, nu, L)

        # forward staple
        term1 = (
            U[x][nu] @
            U[xp_nu][mu] @
            dag(U[xp_mu][nu])
        )

        # backward staple
        term2 = (
            dag(U[xm_nu][nu]) @
            U[xm_nu][mu] @
            U[neighbors(xm_nu, mu, L)[0]][nu]
        )

        S += term1 + term2
    return S

# ============================================================
# Metropolis
# ============================================================

def metropolis_sweep(U, beta, eps, rng, L):
    accept = 0
    for x in U:
        for mu in range(4):
            old = U[x][mu]
            R = project_to_su2(np.eye(2) + eps*(rng.normal(size=(2,2)) + 1j*rng.normal(size=(2,2))))
            Unew = R @ old

            Stap = staple(U, x, mu, L)

            deltaS = -beta * np.real(
                np.trace((Unew - old) @ Stap)
            )

            if deltaS < 0 or rng.random() < np.exp(-deltaS):
                U[x][mu] = Unew
                accept += 1

    return accept / (len(U) * 4)

# ============================================================
# APE smearing
# ============================================================

def ape_smear(U, L, alpha=0.5):
    U_new = {}
    for x in U:
        U_new[x] = {}
        for mu in range(4):
            S = staple(U, x, mu, L)
            V = (1 - alpha) * U[x][mu] + (alpha / 6.0) * S
            U_new[x][mu] = project_to_su2(V)
    return U_new

# ============================================================
# Glueball operator
# ============================================================

def plaquette(U, x, mu, nu, L):
    xp_mu, _ = neighbors(x, mu, L)
    xp_nu, _ = neighbors(x, nu, L)

    return np.trace(
        U[x][mu] @
        U[xp_mu][nu] @
        dag(U[xp_nu][mu]) @
        dag(U[x][nu])
    )

def timeslice_plaquette_operator(U, L):
    """O(t)=sum_{x in spatial slice t} sum_{mu<nu} Re Tr U_{mu nu}(x)."""
    O = np.zeros(L, dtype=np.float64)
    for x in U:
        t = x[0]
        s = 0.0
        for mu in range(4):
            for nu in range(mu+1, 4):
                s += float(np.real(plaquette(U, x, mu, nu, L)))
        O[t] += s / (L**3)
    return O

def connected_timeslice_corr(O):
    """C(dt)=<O(t)O(t+dt)>_t - <O>^2 with periodic time."""
    L = len(O)
    mean = float(np.mean(O))
    C = np.zeros(L, dtype=np.float64)
    for dt in range(L):
        C[dt] = float(np.mean(O * np.roll(O, -dt)) - mean*mean)
    return C

# ============================================================
# Effective mass
# ============================================================

def stable_effective_mass(C):
    m = []
    for t in range(1, len(C)):
        if C[t] <= 0 or C[t-1] <= 0:
            m.append(np.nan)
        else:
            val = np.log(C[t-1] / C[t])
            if val < 0 or val > 10:
                m.append(np.nan)
            else:
                m.append(val)
    return np.array(m)

# ============================================================
# Run simulation
# ============================================================

def run(L, beta, therm, meas_sweeps, stride, eps, seed, outfile):

    rng = np.random.default_rng(seed)

    # initialize gauge field
    U = {}
    for x0 in range(L):
        for x1 in range(L):
            for x2 in range(L):
                for x3 in range(L):
                    x = (x0,x1,x2,x3)
                    U[x] = {}
                    for mu in range(4):
                        U[x][mu] = su2_random(rng)

    print("\nThermalizing...")
    for i in range(therm):
        metropolis_sweep(U, beta, eps, rng, L)

    print("Applying 1-step APE smearing...")
    U = ape_smear(U, L, alpha=0.5)

    print("Starting measurements...")
    C_acc = np.zeros(L)
    n_meas = 0

    for i in range(meas_sweeps):
        metropolis_sweep(U, beta, eps, rng, L)
        if i % stride == 0:
            O = timeslice_plaquette_operator(U, L)
            C_acc += connected_timeslice_corr(O)
            n_meas += 1

    C = C_acc / max(1, n_meas)
    m_eff = stable_effective_mass(C)

    print("\nGlueball correlator:")
    for t in range(len(C)):
        print(f"{t:2d}  {C[t]:.6e}")

    print("\nEffective mass:")
    for t in range(len(m_eff)):
        print(f"{t+1:2d}  {m_eff[t]}")

    np.savez(outfile + ".npz", C=C, m_eff=m_eff)
    print(f"\nSaved to {outfile}.npz")

    return C, m_eff

# ============================================================

if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("--L", type=int, default=6)
    parser.add_argument("--beta", type=float, default=0.6)
    parser.add_argument("--therm", type=int, default=1500)
    parser.add_argument("--meas_sweeps", type=int, default=8000)
    parser.add_argument("--stride", type=int, default=10)
    parser.add_argument("--eps", type=float, default=1.4)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--outfile", type=str, default="glueball_output")

    args = parser.parse_args()

    run(
        L=args.L,
        beta=args.beta,
        therm=args.therm,
        meas_sweeps=args.meas_sweeps,
        stride=args.stride,
        eps=args.eps,
        seed=args.seed,
        outfile=args.outfile
    )
