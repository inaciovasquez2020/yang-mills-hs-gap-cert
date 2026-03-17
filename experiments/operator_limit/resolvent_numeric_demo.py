import numpy as np

def resolvent(H,lam):
    return np.linalg.inv(H + lam*np.eye(H.shape[0]))

for n in [10,20,40]:
    H=np.diag(np.arange(1,n+1))
    R=resolvent(H,1.0)
    print(n,np.trace(R))
