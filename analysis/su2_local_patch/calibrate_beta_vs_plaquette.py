import numpy as np
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
    sweeps = 10
    eps = 0.25
    trials = 10

    betas = [1.5, 2.0, 2.3, 2.6, 3.0]

    for beta in betas:
        vals = []
        for j in range(trials):
            U = make_random_U(L, j + 1000)
            U, _ = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=2000+j)
            vals.append(plaquette_avg(U, L))
        print(beta, float(np.mean(vals)))

if __name__ == "__main__":
    main()
