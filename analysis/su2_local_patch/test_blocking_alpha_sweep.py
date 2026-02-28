import numpy as np
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d
from analysis.su2_local_patch.test_blocking_beta_flow import idx, random_su2, plaquette_avg

L = 4
b = 2
beta = 2.3

U = np.zeros((L**4,4,2,2), dtype=np.complex128)
for x in range(L):
    for y in range(L):
        for z in range(L):
            for t in range(L):
                for mu in range(4):
                    U[idx(x,y,z,t,L),mu] = random_su2()

fine = plaquette_avg(U,L)

for alpha in [0.0, 0.2, 0.5, 1.0]:
    Uc = block_weighted_covariant_4d(U,L,b,beta,alpha_override=alpha)
    coarse = plaquette_avg(Uc,L//b)
    print("alpha =", alpha, "shift =", coarse - fine)
