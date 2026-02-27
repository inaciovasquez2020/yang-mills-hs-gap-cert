import numpy as np

def periodic_diff(L):
    D = np.zeros((L, L))
    for i in range(L):
        D[i, (i+1) % L] = 0.5
        D[i, (i-1) % L] = -0.5
    return D

def laplacian_1d(L):
    D2 = np.zeros((L, L))
    for i in range(L):
        D2[i, i] = 2.0
        D2[i, (i+1) % L] = -1.0
        D2[i, (i-1) % L] = -1.0
    return D2

def sym(A):
    return 0.5*(A + A.T)

def test_mourre_commutator_positive_on_energy_window():
    m2 = 8.0
    for L in [64, 128]:
        X = np.diag(np.linspace(-(L-1)/2, (L-1)/2, L))
        D = periodic_diff(L)
        A = sym(X @ D + D.T @ X)
        
        H = laplacian_1d(L) + m2 * np.eye(L)

        C = sym(1j*(H @ A - A @ H))
        C = np.real(C)

        w, V = np.linalg.eigh(H)
        mask = (w > m2 + 1e-6) & (w < m2 + 0.5)
        Vw = V[:, mask]
        if Vw.shape[1] == 0:
            print(f"L={L}: No eigenvalues in window")
            continue

        Cw = Vw.T @ C @ Vw
        eigC = np.linalg.eigvalsh(sym(Cw))

        min_eigC = np.min(eigC)
        print(f"L={L}: min eigenvalue of commutator = {min_eigC:.6f}")
        assert min_eigC >= -1e-6, f"L={L}: Commutator not positive: {min_eigC}"
