import numpy as np

def random_projection_norm(n, k):
    A = np.random.randn(n, k)
    Q, _ = np.linalg.qr(A)
    P = Q @ Q.T
    w = np.linalg.eigvalsh(P)
    return max(w)

for k in [2,4,8,16]:
    print("k",k,"norm",random_projection_norm(100,k))
