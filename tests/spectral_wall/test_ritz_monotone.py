import numpy as np

def Vk_scalar(r: np.ndarray, k: int) -> np.ndarray:
    t = np.tan(r / 2.0)
    sec2 = 1.0 / (np.cos(r / 2.0) ** 2)
    return 0.5 * k * sec2 * (t ** 2)

def ritz_min(d: int, k: int, ell: int, m: int = 12, n: int = 1200, eps: float = 1e-3):
    r = np.linspace(eps, np.pi - eps, n)
    h = r[1] - r[0]
    sinr = np.sin(r)
    w = sinr ** (d - 1)

    V = 6.0 + Vk_scalar(r, k) + (ell * (ell + d - 2)) / (sinr ** 2)

    def basis(j):
        a = ell + j
        return (sinr ** a) * np.exp(-r)

    B = np.stack([basis(j) for j in range(m)], axis=1)
    dB = np.gradient(B, h, axis=0)

    G = np.zeros((m, m))
    A = np.zeros((m, m))

    for i in range(m):
        for j in range(m):
            G[i, j] = np.sum(w * B[:, i] * B[:, j]) * h
            A[i, j] = (
                np.sum(w * dB[:, i] * dB[:, j]) * h
                + np.sum(w * V * B[:, i] * B[:, j]) * h
            )

    evals, evecs = np.linalg.eigh(G)
    mask = evals > 1e-10
    Q = evecs[:, mask] @ np.diag(1.0 / np.sqrt(evals[mask]))

    M = Q.T @ A @ Q
    return float(np.linalg.eigvalsh(M)[0])

def test_ritz_lower_bound_stable_and_positive():
    d = 4
    ms = [6, 8, 10, 12]
    for k in [1, 2, 3]:
        for ell in [0, 1, 2, 3]:
            vals = np.array([ritz_min(d=d, k=k, ell=ell, m=m) for m in ms])
            assert vals[-1] <= vals[0] + 1e-5
            assert vals[-1] > 1.0
