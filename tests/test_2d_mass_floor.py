import numpy as np

def laplacian_2d(L):
    N = L * L
    Δ = np.zeros((N, N))
    def idx(x, y): return x * L + y
    for x in range(L):
        for y in range(L):
            i = idx(x, y)
            Δ[i, i] = 4
            for dx, dy in [(-1,0),(1,0),(0,-1),(0,1)]:
                j = idx((x+dx)%L, (y+dy)%L)
                Δ[i, j] = -1
    return Δ

def test_2d_mass_floor():
    m2 = 8.0
    for L in [4, 6, 8, 12]:
        Δ = laplacian_2d(L)
        eig_Δ = np.linalg.eigvalsh(Δ)
        min_eig_Δ = np.min(eig_Δ)
        assert min_eig_Δ >= -1e-10, f"L={L}: Laplacian has negative eigenvalue {min_eig_Δ}"
        
        H = Δ + m2 * np.eye(L*L)
        eig_H = np.linalg.eigvalsh(H)
        min_eig_H = np.min(eig_H)
        assert min_eig_H >= m2 - 1e-10, f"L={L}: min eigenvalue {min_eig_H} < {m2}"
        
        print(f"L={L:3d}: min eig(Δ)={min_eig_Δ:10.6f}, min eig(H)={min_eig_H:10.6f} (≥ {m2})")

if __name__ == "__main__":
    test_2d_mass_floor()
