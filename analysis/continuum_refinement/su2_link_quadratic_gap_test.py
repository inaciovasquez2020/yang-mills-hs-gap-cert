import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

def site_index(x,y,z,w,L):
    return ((x%L)*L*L*L +
            (y%L)*L*L +
            (z%L)*L +
            (w%L))

def link_index(x,y,z,w,mu,a,L):
    return site_index(x,y,z,w,L)*12 + mu*3 + a

def build_su2_quadratic_curl(L):
    N_sites = L**4
    N_links = 12*N_sites
    rows, cols, data = [], [], []

    def add(i,j,val):
        rows.append(i); cols.append(j); data.append(val)

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for w in range(L):
                    for mu in range(4):
                        for nu in range(mu+1,4):
                            for a in range(3):

                                l1 = link_index(x,y,z,w,mu,a,L)
                                l2 = link_index(x,y,z,w,nu,a,L)

                                xp,yp,zp,wp = x,y,z,w
                                if mu==0: xp+=1
                                if mu==1: yp+=1
                                if mu==2: zp+=1
                                if mu==3: wp+=1
                                l3 = link_index(xp,yp,zp,wp,nu,a,L)

                                xp2,yp2,zp2,wp2 = x,y,z,w
                                if nu==0: xp2+=1
                                if nu==1: yp2+=1
                                if nu==2: zp2+=1
                                if nu==3: wp2+=1
                                l4 = link_index(xp2,yp2,zp2,wp2,mu,a,L)

                                add(l1,l1,1)
                                add(l2,l2,1)
                                add(l3,l3,1)
                                add(l4,l4,1)

                                add(l1,l2,-1)
                                add(l2,l3,-1)
                                add(l3,l4,-1)
                                add(l4,l1,-1)

    H = sp.csr_matrix((data,(rows,cols)),shape=(N_links,N_links))
    H = (H + H.T) * 0.5
    return H

def compute_gap(L):
    H = build_su2_quadratic_curl(L)
    vals = spla.eigsh(H,k=20,which='SM',return_eigenvectors=False)
    vals = np.sort(np.real(vals))
    for v in vals:
        if v > 1e-8:
            return float(v)
    return 0.0

print("L   DOF         Gap        Gap*L^2")
print("------------------------------------------------")

for L in [3,4,5]:
    gap = compute_gap(L)
    print(f"{L:2d} {12*L**4:9d} {gap:12.6f} {gap*(L**2):12.6f}")
