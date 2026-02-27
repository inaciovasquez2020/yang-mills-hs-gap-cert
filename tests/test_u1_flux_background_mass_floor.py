import numpy as np
from math import pi

def idx(x, y, L):
    return (x % L) + L * (y % L)

def build_G(L):
    nV = L * L
    nE = 2 * L * L
    G = np.zeros((nE, nV))
    def e_x(x, y): return idx(x, y, L)
    def e_y(x, y): return L * L + idx(x, y, L)
    for y in range(L):
        for x in range(L):
            v = idx(x, y, L)
            ex = e_x(x, y)
            G[ex, v] = -1
            G[ex, idx(x + 1, y, L)] = 1
            ey = e_y(x, y)
            G[ey, v] = -1
            G[ey, idx(x, y + 1, L)] = 1
    return G

def build_C(L):
    nE = 2 * L * L
    nF = L * L
    C = np.zeros((nF, nE))
    def e_x(x, y): return idx(x, y, L)
    def e_y(x, y): return L * L + idx(x, y, L)
    for y in range(L):
        for x in range(L):
            f = idx(x, y, L)
            C[f, e_x(x, y)] = 1
            C[f, e_y(x + 1, y)] = 1
            C[f, e_x(x, y + 1)] = -1
            C[f, e_y(x, y)] = -1
    return C

def orth_proj_svd(A, tol=1e-12):
    U, s, _ = np.linalg.svd(A, full_matrices=False)
    if s.size == 0:
        return np.zeros((A.shape[0], A.shape[0]))
    r = int(np.sum(s > tol * s[0]))
    if r == 0:
        return np.zeros((A.shape[0], A.shape[0]))
    Ur = U[:, :r]
    return Ur @ Ur.T

def coexact_projector(L):
    G = build_G(L)
    C = build_C(L)
    PG = orth_proj_svd(G)
    KC = orth_proj_svd(C.T)
    I = np.eye(PG.shape[0])
    Pco = KC @ (I - PG)
    return 0.5 * (Pco + Pco.T)

def unpack_edges(u, L):
    n = L * L
    ax = u[:n].reshape((L, L))
    ay = u[n:].reshape((L, L))
    return ax, ay

def pack_edges(ax, ay):
    return np.concatenate([ax.reshape(-1), ay.reshape(-1)])

def plaquette_angles(ax, ay, L):
    P = np.zeros((L, L))
    for y in range(L):
        for x in range(L):
            p = ax[x, y] + ay[(x + 1) % L, y] - ax[x, (y + 1) % L] - ay[x, y]
            P[x, y] = (p + pi) % (2 * pi) - pi
    return P

def wilson_action_u1(u, L, beta):
    ax, ay = unpack_edges(u, L)
    P = plaquette_angles(ax, ay, L)
    return float(beta * np.sum(1.0 - np.cos(P)))

def numeric_hessian(f, u0, eps):
    n = u0.size
    H = np.zeros((n, n))
    f0 = f(u0)
    for i in range(n):
        ei = np.zeros(n); ei[i] = 1.0
        fp = f(u0 + eps * ei)
        fm = f(u0 - eps * ei)
        H[i, i] = (fp - 2 * f0 + fm) / (eps * eps)
        for j in range(i + 1, n):
            ej = np.zeros(n); ej[j] = 1.0
            fpp = f(u0 + eps * ei + eps * ej)
            fpm = f(u0 + eps * ei - eps * ej)
            fmp = f(u0 - eps * ei + eps * ej)
            fmm = f(u0 - eps * ei - eps * ej)
            Hij = (fpp - fpm - fmp + fmm) / (4 * eps * eps)
            H[i, j] = Hij
            H[j, i] = Hij
    return 0.5 * (H + H.T)

def background_flux_u0(L, q):
    ax = np.zeros((L, L))
    ay = np.zeros((L, L))
    for y in range(L):
        for x in range(L):
            ay[x, y] = 2 * pi * q * x / (L * L)
    return pack_edges(ax, ay)

def min_pos_eig(M, tol=1e-7):
    w = np.linalg.eigvalsh(0.5 * (M + M.T))
    pos = w[w > tol]
    if pos.size == 0:
        return None
    return float(np.min(pos))

def test_u1_flux_background_coexact_mass_floor():
    beta = 1.0
    q = 1
    eps = 1e-3
    m2 = 8.0 * beta
    for L in [4, 6, 8]:
        u0 = background_flux_u0(L, q)
        f = lambda u: wilson_action_u1(u, L, beta)
        H = numeric_hessian(f, u0, eps=eps)
        Hm = H + m2 * np.eye(H.shape[0])
        P = coexact_projector(L)
        Hc = P @ Hm @ P
        lam = min_pos_eig(Hc)
        assert lam is not None, f"L={L}: no positive eigenvalues in coexact sector"
        assert lam >= m2 - 1e-4, f"L={L}: min coexact eig {lam} < {m2}"

if __name__ == "__main__":
    test_u1_flux_background_coexact_mass_floor()
