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

def test_2d_transverse_gap_scaling():
    sizes = [4, 6, 8, 10, 12]
    scaled = []
    print("Testing transverse gauge sector gap scaling")
    print("="*50)
    for L in sizes:
        G = build_G(L)
        C = build_C(L)
        L1 = (G @ G.T) + (C.T @ C)
        PG = orth_proj(G)
        KC = orth_proj(C.T)
        P_trans = np.eye(PG.shape[0]) - PG - KC
        Lt = P_trans @ L1 @ P_trans
        eig = np.linalg.eigvalsh(Lt)
        pos = eig[eig > 1e-8]
        if len(pos) > 0:
            lam = np.min(pos)
            scaled_val = lam * (L**2)
            scaled.append(scaled_val)
            print(f"L={L:3d}: λ_min = {lam:.8f}, λ_min × L² = {scaled_val:.4f}")
        else:
            print(f"L={L:3d}: No positive eigenvalues found")
    
    if len(scaled) > 1:
        ratios = np.array(scaled)
        ratio_max_min = np.max(ratios) / np.min(ratios)
        print(f"\nRatio max/min = {ratio_max_min:.4f}")
        assert ratio_max_min < 2.5, f"Scaling violation: {ratio_max_min} >= 2.5"
        print("✓ Scaling consistent with 1/L²")
    else:
        print("⚠ Insufficient data for scaling analysis")

if __name__ == "__main__":
    test_2d_transverse_gap_scaling()
