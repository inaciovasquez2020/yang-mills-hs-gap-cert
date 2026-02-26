import numpy as np

def orth_projector(K):
    Q, _ = np.linalg.qr(K)
    return Q @ Q.conj().T

def test_coercivity(H, K, tol=1e-10):
    P = orth_projector(K)
    I = np.eye(H.shape[0])
    H_phys = (I - P) @ H @ (I - P)
    eigvals = np.linalg.eigvalsh(H_phys)
    eigvals = eigvals[np.abs(eigvals) > tol]
    if len(eigvals) == 0:
        return False, 0.0
    m = np.min(eigvals)
    return m > 0, m

H = np.diag([0,0,2,3,5])
K = np.eye(5)[:, :2]

ok, gap = test_coercivity(H, K)
print("Coercive:", ok)
print("Physical gap m =", gap)
