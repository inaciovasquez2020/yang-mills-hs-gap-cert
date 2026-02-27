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

def su2_adjoint_generators():
    J1 = np.array([[0,0,0],[0,0,-1],[0,1,0]], dtype=float)
    J2 = np.array([[0,0,1],[0,0,0],[-1,0,0]], dtype=float)
    J3 = np.array([[0,-1,0],[1,0,0],[0,0,0]], dtype=float)
    return [J1, J2, J3]

def test_su2_coupling_perturbation_keeps_mass_floor():
    m2 = 8.0
    g = 0.25
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
        L1t = 0.5*(L1t + L1t.T)

        Nc = 3
        H0 = np.kron(np.eye(Nc), L1t) + m2 * np.eye(Nc * L1t.shape[0])

        gens = su2_adjoint_generators()
        J = gens[0] + gens[1] + gens[2]
        J = 0.5*(J - J.T)

        M = L1t
        M = 0.5*(M + M.T)
        K = np.kron(J, M)
        K = 0.5*(K + K.T)

        H = H0 + g * K

        lam = min_pos_eig(H)
        assert lam is not None, f"L={L}: No positive eigenvalues found"
        assert lam >= m2 - 1e-6, f"L={L}: λ_min={lam} < {m2}"
        print(f"L={L}: λ_min={lam:.6f} (with SU(2) coupling) ✓")
