import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spla

def Vk_scalar(r: np.ndarray, k: int) -> np.ndarray:
    t = np.tan(r / 2.0)
    sec2 = 1.0 / (np.cos(r / 2.0) ** 2)
    return 0.5 * k * sec2 * (t ** 2)

def build_operator(d: int, k: int, ell: int, n: int = 800, eps: float = 1e-4):
    r = np.linspace(eps, np.pi - eps, n)
    h = r[1] - r[0]

    sinr = np.sin(r)

    V = 6.0 + Vk_scalar(r, k) + (ell * (ell + d - 2)) / (sinr ** 2)

    main = np.zeros(n)
    upper = np.zeros(n - 1)
    lower = np.zeros(n - 1)

    for i in range(1, n - 1):
        main[i] = 2.0 / h**2 + V[i]
        upper[i] = -1.0 / h**2
        lower[i - 1] = -1.0 / h**2

    main[0] = 1e12
    main[-1] = 1e12

    A = sp.diags([lower, main, upper], offsets=[-1, 0, 1], format="csc")
    return A

def smallest_eigenvalue(d: int, k: int, ell: int, n: int = 800) -> float:
    A = build_operator(d=d, k=k, ell=ell, n=n)
    vals = spla.eigsh(A, k=1, which="SA", return_eigenvectors=False, tol=1e-9)
    return float(vals[0])

if __name__ == "__main__":
    for k in [1, 2, 3]:
        for ell in [0, 1, 2, 3]:
            lam = smallest_eigenvalue(d=4, k=k, ell=ell, n=800)
            print(f"k={k} ell={ell} lambda_min={lam:.6e}")
