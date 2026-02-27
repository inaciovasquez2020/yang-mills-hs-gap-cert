import numpy as np

def idx(x, y, L):
    return (x % L) + L * (y % L)

def build_G(L):
    nV = L * L
    nE = 2 * L * L
    G = np.zeros((nE, nV))
    def e_x(x, y): return idx(x, y, L)
    def e_y(x, y): return L*L + idx(x, y, L)
    for y in range(L):
        for x in range(L):
            v = idx(x, y, L)
            ex = e_x(x, y)
            G[ex, v] = -1
            G[ex, idx(x+1, y, L)] = 1
            ey = e_y(x, y)
            G[ey, v] = -1
            G[ey, idx(x, y+1, L)] = 1
    return G

def build_C(L):
    nE = 2 * L * L
    nF = L * L
    C = np.zeros((nF, nE))
    def e_x(x, y): return idx(x, y, L)
    def e_y(x, y): return L*L + idx(x, y, L)
    for y in range(L):
        for x in range(L):
            f = idx(x, y, L)
            C[f, e_x(x, y)] = 1
            C[f, e_y(x+1, y)] = 1
            C[f, e_x(x, y+1)] = -1
            C[f, e_y(x, y)] = -1
    return C

def orth_proj(A, tol=1e-12):
    Q, R = np.linalg.qr(A)
    diag = np.abs(np.diag(R))
    r = int(np.sum(diag > tol))
    if r == 0:
        return np.zeros((A.shape[0], A.shape[0]))
    Qr = Q[:, :r]
    return Qr @ Qr.T

def min_pos_eig(M, tol=1e-8):
    eig = np.linalg.eigvalsh(0.5*(M+M.T))
    pos = eig[eig > tol]
    if len(pos) == 0:
        return None
    return float(np.min(pos))

def test_color_block_extension_preserves_mass_floor():
    m2 = 8.0
    Nc = 3
    for L in [4, 6, 8]:
        G = build_G(L)
        C = build_C(L)
        L1 = (G @ G.T) + (C.T @ C)
        
        PG = orth_proj(G)
        KC = orth_proj(C.T)
        I = np.eye(L1.shape[0])
        P_trans = I - PG - KC
        P_trans = 0.5*(P_trans + P_trans.T)

        L1t = P_trans @ L1 @ P_trans
        L1c = np.kron(np.eye(Nc), L1t)
        Hc = L1c + m2 * np.eye(L1c.shape[0])

        lam = min_pos_eig(Hc)
        assert lam is not None, f"L={L}: No positive eigenvalues found"
        assert lam >= m2 - 1e-10, f"L={L}: λ_min={lam} < {m2}"
        print(f"L={L}: λ_min={lam:.6f} ✓")
