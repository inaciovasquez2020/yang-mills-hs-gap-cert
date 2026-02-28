import numpy as np
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d

def idx(x,y,z,t,L):
    return ((x*L + y)*L + z)*L + t

def random_su2():
    a = np.random.randn(4)
    a /= np.linalg.norm(a)
    a0,a1,a2,a3 = a
    return np.array([
        [a0+1j*a3,  a2+1j*a1],
        [-a2+1j*a1, a0-1j*a3]
    ], dtype=np.complex128)

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

fine_plaq = plaquette_avg(U, L)

Uc = block_weighted_covariant_4d(U, L, b, beta)
coarse_plaq = plaquette_avg(Uc, L//b)

print("Fine plaquette avg:", fine_plaq)
print("Coarse plaquette avg:", coarse_plaq)
print("Shift:", coarse_plaq - fine_plaq)
