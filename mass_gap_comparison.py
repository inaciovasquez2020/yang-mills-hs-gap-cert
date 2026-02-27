import numpy as np

def laplacian_matrix(L):
    Δ = np.zeros((L, L))
    for i in range(L):
        Δ[i, i] = 2
        Δ[i, (i - 1) % L] = -1
        Δ[i, (i + 1) % L] = -1
    return Δ

def hessian_with_mass(L, m2):
    return laplacian_matrix(L) + m2 * np.eye(L)

def compare():
    print("Comparison: Laplacian vs Hessian with mass")
    print("=" * 60)
    print(f"{'L':>4} {'Laplacian λ_min':>18} {'× L²':>10} {'Hessian λ_min':>18}")
    print("-" * 60)

    m2 = 8.0

    for L in [4, 6, 8, 10, 16, 32, 64, 128, 256]:
        Δ = laplacian_matrix(L)
        λ_lap = np.min(np.linalg.eigvalsh(Δ))
        H = hessian_with_mass(L, m2)
        λ_hess = np.min(np.linalg.eigvalsh(H))
        print(f"{L:4d} {λ_lap:18.8f} {λ_lap * L * L:10.4f} {λ_hess:18.8f}")

if __name__ == "__main__":
    compare()
