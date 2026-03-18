import numpy as np

def resolvent(H,lam):
    return np.linalg.inv(H + lam*np.eye(H.shape[0]))

H1=np.diag([0,1,2])
H2=np.diag([0,1.01,2.02])

print(np.linalg.norm(resolvent(H1,1)-resolvent(H2,1)))
