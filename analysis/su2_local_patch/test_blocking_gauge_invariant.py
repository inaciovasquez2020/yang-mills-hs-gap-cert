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

def coarse_plaquette(Uc, Lc):
    # compute trace of one plaquette at origin in mu=0, nu=1 plane
    s = idx(0,0,0,0,Lc)
    U01 = Uc[s,0]
    s1 = idx(1%Lc,0,0,0,Lc)
    U12 = Uc[s1,1]
    s2 = idx(0,1%Lc,0,0,Lc)
    U23 = Uc[s2,0]
    U30 = Uc[s,1]
    return np.trace(U01 @ U12 @ np.linalg.inv(U23) @ np.linalg.inv(U30)).real

def gauge_transform(U, L):
    G = np.zeros((L**4,2,2), dtype=np.complex128)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    G[idx(x,y,z,t,L)] = random_su2()

    U2 = np.zeros_like(U)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    s = idx(x,y,z,t,L)
                    for mu in range(4):
                        xp = x + (1 if mu==0 else 0)
                        yp = y + (1 if mu==1 else 0)
                        zp = z + (1 if mu==2 else 0)
                        tp = t + (1 if mu==3 else 0)
                        sp = idx(xp%L, yp%L, zp%L, tp%L, L)
                        U2[s,mu] = G[s] @ U[s,mu] @ np.linalg.inv(G[sp])
    return U2

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

Uc1 = block_weighted_covariant_4d(U,L,b,beta)
U_g = gauge_transform(U,L)
Uc2 = block_weighted_covariant_4d(U_g,L,b,beta)

p1 = coarse_plaquette(Uc1, L//b)
p2 = coarse_plaquette(Uc2, L//b)

print("Plaquette difference:", abs(p1 - p2))
