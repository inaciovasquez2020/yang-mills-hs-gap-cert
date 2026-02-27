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
    Qr = Q[:, :r]
    return Qr @ Qr.T

def min_pos_eig(M, eps=1e-8):
    eig = np.linalg.eigvalsh(M)
    pos = eig[eig > eps]
    return None if len(pos) == 0 else float(np.min(pos))

def test_2d_coexact_gap_scales_like_L_inv2():
    sizes = [4, 6, 8, 10, 12]
    scaled = []
    for L in sizes:
        G = build_G(L)
        C = build_C(L)

        PG = orth_proj(G)
        KC = orth_proj(C.T)

        I = np.eye(PG.shape[0])

        P_exact = PG
        P_coexact = KC @ (I - PG)
        P_coexact = 0.5 * (P_coexact + P_coexact.T)

        L1 = (G @ G.T) + (C.T @ C)

        Lc = P_coexact @ L1 @ P_coexact
        lam = min_pos_eig(Lc)
        assert lam is not None, f"L={L}: no positive eigenvalues in coexact sector"

        scaled.append(lam * (L**2))

    ratios = np.array(scaled)
    assert np.max(ratios) / np.min(ratios) < 2.5
