import numpy as np

def build_1d_gradient(L):
    # Edges indexed same as vertices (periodic)
    G = np.zeros((L, L))
    for i in range(L):
        G[i, i] = -1
        G[i, (i+1)%L] = 1
    return G

def test_vector_gauge_laplacian():
    m2 = 8.0
    for L in [4, 8, 16, 32]:
        G = build_1d_gradient(L)
        L_edge = G @ G.T

        eig = np.linalg.eigvalsh(L_edge)
        
        # Kernel dimension should be 1 (gauge mode)
        zero_modes = np.sum(np.abs(eig) < 1e-8)
        assert zero_modes == 1, f"L={L}: Expected 1 zero mode, found {zero_modes}"
        print(f"L={L:3d}: Zero mode count = {zero_modes} ✓")

        # Project to divergence-free (orthogonal to kernel)
        N = L
        ones = np.ones((N,1))
        P = np.eye(N) - (1.0/N)*(ones@ones.T)

        L_proj = P @ L_edge @ P
        eig_proj = np.linalg.eigvalsh(L_proj)

        positive = eig_proj[eig_proj > 1e-8]
        if len(positive) > 0:
            min_pos = np.min(positive)
            print(f"L={L:3d}: min positive eigenvalue after projection = {min_pos:.6f}")
            assert min_pos >= -1e-10

        # Add mass - this is the Wilson action's constant term
        H = L_edge + m2 * np.eye(N)
        H_proj = P @ H @ P
        eig_H = np.linalg.eigvalsh(H_proj)
        positive_H = eig_H[eig_H > 1e-8]
        min_H = np.min(positive_H)
        print(f"L={L:3d}: min eigenvalue with mass = {min_H:.6f} (≥ {m2})")
        assert min_H >= m2 - 1e-10, f"L={L}: min eigenvalue {min_H} < {m2}"
        print()

if __name__ == "__main__":
    test_vector_gauge_laplacian()
