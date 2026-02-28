import numpy as np
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d
from analysis.su2_local_patch.metropolis_su2_4d import idx, random_su2, thermalize_metropolis

def plaquette_avg(U, L):
    total = 0.0
    count = 0
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s = idx(x,y,z,t,L)
                    U01 = U[s,0]
                    s1 = idx((x+1)%L,y,z,t,L)
                    U12 = U[s1,1]
                    s2 = idx(x,(y+1)%L,z,t,L)
                    U23 = U[s2,0]
                    U30 = U[s,1]
                    total += np.trace(U01 @ U12 @ np.linalg.inv(U23) @ np.linalg.inv(U30)).real
                    count += 1
    return total / count

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
    L = 6
    b = 3
    beta = 2.3
    trials = 25
    base_seed = 0

    sweeps = 10
    eps = 0.25

    fine_vals = []
    coarse_vals = []
    shifts = []
    accs = []

    for j in range(trials):
        U = make_random_U(L, base_seed + j)
        U, acc = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=10_000 + j)
        accs.append(acc)

        fine = plaquette_avg(U, L)
        Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=0.0)
        coarse = plaquette_avg(Uc, L//b)

        fine_vals.append(fine)
        coarse_vals.append(coarse)
        shifts.append(coarse - fine)

    fine_vals = np.array(fine_vals)
    coarse_vals = np.array(coarse_vals)
    shifts = np.array(shifts)
    accs = np.array(accs)

    def stats(x):
        return float(np.mean(x)), float(np.std(x, ddof=1)), float(np.min(x)), float(np.max(x))

    mf, sf, mnf, mxf = stats(fine_vals)
    mc, sc, mnc, mxc = stats(coarse_vals)
    ms, ss, mns, mxs = stats(shifts)
    ma, sa, mna, mxa = stats(accs)

    print("L b beta trials seed0 sweeps eps")
    print(L, b, beta, trials, base_seed, sweeps, eps)
    print("accept_mean accept_sd accept_min accept_max")
    print(ma, sa, mna, mxa)
    print("fine_mean fine_sd fine_min fine_max")
    print(mf, sf, mnf, mxf)
    print("coarse_mean coarse_sd coarse_min coarse_max")
    print(mc, sc, mnc, mxc)
    print("shift_mean shift_sd shift_min shift_max")
    print(ms, ss, mns, mxs)

if __name__ == "__main__":
    main()
