import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

def lattice_gauge_laplacian(L,a,theta):
    N = L**4
    def idx(x,y,z,w):
        return ((x%L)*L*L*L +
                (y%L)*L*L +
                (z%L)*L +
                (w%L))
    rows, cols, data = [], [], []
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for w in range(L):
                    i = idx(x,y,z,w)
                    rows.append(i); cols.append(i); data.append(8.0/(a*a))
                    for dx,dy,dz,dw in [(1,0,0,0),(-1,0,0,0),
                                        (0,1,0,0),(0,-1,0,0),
                                        (0,0,1,0),(0,0,-1,0),
                                        (0,0,0,1),(0,0,0,-1)]:
                        j = idx(x+dx,y+dy,z+dz,w+dw)
                        phase = np.exp(1j*theta*dx)
                        rows.append(i); cols.append(j); data.append(-phase/(a*a))
    return sp.csr_matrix((data,(rows,cols)),shape=(N,N),dtype=complex)

def compute_gap(L,a,theta):
    A = lattice_gauge_laplacian(L,a,theta)
    vals = spla.eigsh(A,k=2,which='SM',return_eigenvectors=False)
    vals = np.sort(np.real(vals))
    return float(vals[1])

print("L   theta   Gap")
print("---------------------------")

for L in [6,8,10]:
    a = 1.0/L
    for theta in [0.0,0.5,1.0]:
        gap = compute_gap(L,a,theta)
        print(f"{L:2d} {theta:6.2f} {gap:12.6f}")
