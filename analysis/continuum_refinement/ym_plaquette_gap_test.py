import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

def idx(x,y,z,w,L):
    return ((x%L)*L*L*L +
            (y%L)*L*L +
            (z%L)*L +
            (w%L))

def laplacian_4d(L,a):
    N = L**4
    rows, cols, data = [], [], []
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for w in range(L):
                    i = idx(x,y,z,w,L)
                    rows.append(i); cols.append(i); data.append(8.0/(a*a))
                    for dx,dy,dz,dw in [(1,0,0,0),(-1,0,0,0),
                                        (0,1,0,0),(0,-1,0,0),
                                        (0,0,1,0),(0,0,-1,0),
                                        (0,0,0,1),(0,0,0,-1)]:
                        j = idx(x+dx,y+dy,z+dz,w+dw,L)
                        rows.append(i); cols.append(j); data.append(-1.0/(a*a))
    return sp.csr_matrix((data,(rows,cols)),shape=(N,N))

def plaquette_term(L,beta):
    N = L**4
    rows, cols, data = [], [], []
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for w in range(L):
                    i = idx(x,y,z,w,L)
                    rows.append(i); cols.append(i); data.append(6.0*beta)
    return sp.csr_matrix((data,(rows,cols)),shape=(N,N))

def compute_gap(L,beta):
    a = 1.0/L
    H = laplacian_4d(L,a) + plaquette_term(L,beta)
    vals = spla.eigsh(H,k=2,which='SM',return_eigenvectors=False)
    vals = np.sort(np.real(vals))
    return float(vals[1])

print("L   beta   Gap")
print("---------------------------")

for L in [6,8,10]:
    for beta in [0.0,0.5,1.0]:
        gap = compute_gap(L,beta)
        print(f"{L:2d} {beta:6.2f} {gap:12.6f}")
