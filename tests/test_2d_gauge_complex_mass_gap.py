import numpy as np

def idx(x, y, L):
    return (x % L) + L * (y % L)

def build_G(L):
    nV = L * L
    nE = 2 * L * L
    G = np.zeros((nE, nV))

    def e_x(x, y):
        return idx(x, y, L)

    def e_y(x, y):
        return L * L + idx(x, y, L)

    for y in range(L):
        for x in range(L):
            v = idx(x, y, L)

            ex = e_x(x, y)
            v_to = idx(x + 1, y, L)
            G[ex, v] = -1.0
            G[ex, v_to] = 1.0

            ey = e_y(x, y)
            v_to = idx(x, y + 1, L)
            G[ey, v] = -1.0
            G[ey, v_to] = 1.0

    return G

def build_C(L):
    nE = 2 * L * L
    nF = L * L
    C = np.zeros((nF, nE))

    def e_x(x, y):
        return idx(x, y, L)

    def e_y(x, y):
        return L * L + idx(x, y, L)

    for y in range(L):
        for x in range(L):
            f = idx(x, y, L)

            C[f, e_x(x, y)] = 1.0
            C[f, e_y(x + 1, y)] = 1.0
            C[f, e_x(x, y + 1)] = -1.0
            C[f, e_y(x, y)] = -1.0

    return C

def orth_proj(A, tol=1e-12):
    Q, R = np.linalg.qr(A)
    diag = np.abs(np.diag(R))
    r = int(np.sum(diag > tol))
    Qr = Q[:, :r]
    return Qr @ Qr.T

def test_2d_gauge_complex_mass_gap():
    m2 = 8.0
    for L in [4, 6, 8]:
        G = build_G(L)
        C = build_C(L)

        CG = C @ G
        assert np.linalg.norm(CG) < 1e-10

        L0 = G @ G.T
        L1 = (G @ G.T) + (C.T @ C)

        PG = orth_proj(G)
        KC = orth_proj(C.T)

        P_trans = np.eye(PG.shape[0]) - PG - KC

        Lt = P_trans @ L1 @ P_trans
        eig_Lt = np.linalg.eigvalsh(Lt)
        pos = eig_Lt[eig_Lt > 1e-8]
        if len(pos) > 0:
            assert np.min(pos) >= -1e-10

        Ht = P_trans @ (L1 + m2 * np.eye(L1.shape[0])) @ P_trans
        eig_Ht = np.linalg.eigvalsh(Ht)
        posH = eig_Ht[eig_Ht > 1e-8]
        assert np.min(posH) >= m2 - 1e-10

