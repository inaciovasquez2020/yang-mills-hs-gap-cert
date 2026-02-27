import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

def lattice_4d_laplacian(L,a):
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
                        rows.append(i); cols.append(j); data.append(-1.0/(a*a))
    return sp.csr_matrix((data,(rows,cols)),shape=(N,N))

def compute_gap(L,a):
    A = lattice_4d_laplacian(L,a)
    vals = spla.eigsh(A,k=2,which='SM',return_eigenvectors=False)
    vals = np.sort(vals)
    return float(vals[1])

print("L   a=1/L   Physical Size   Gap")
print("-----------------------------------------")

for L in [4,6,8,10]:
    a = 1.0/L
    gap = compute_gap(L,a)
    print(f"{L:2d} {a:7.4f} {L*a:14.6f} {gap:12.6f}")
