import numpy as np

def Vk_scalar(r: np.ndarray, k: int) -> np.ndarray:
    t = np.tan(r / 2.0)
    sec2 = 1.0 / (np.cos(r / 2.0) ** 2)
    return 0.5 * k * sec2 * (t ** 2)

def rayleigh_quotient(d: int, k: int, ell: int, n: int = 800, eps: float = 1e-3):
    r = np.linspace(eps, np.pi - eps, n)
    h = r[1] - r[0]

    sinr = np.sin(r)
    w = sinr ** (d - 1)

    V = 6.0 + Vk_scalar(r, k) + (ell * (ell + d - 2)) / (sinr ** 2)

    psi = sinr ** ell * np.exp(-r)
    psi /= np.sqrt(np.sum(w * psi**2) * h)

    dpsi = np.gradient(psi, h)

    kinetic = np.sum(w * dpsi**2) * h
    potential = np.sum(w * V * psi**2) * h

    return kinetic + potential

if __name__ == "__main__":
    for k in [1, 2, 3]:
        for ell in [0, 1, 2, 3]:
            q = rayleigh_quotient(d=4, k=k, ell=ell)
            print(f"k={k} ell={ell} Rayleigh={q:.6e}")
