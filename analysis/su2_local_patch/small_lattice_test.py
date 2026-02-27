import numpy as np
import scipy.linalg
from plaquette4.plaquette_model import build_plaquette_patch


def global_test(num_patches=4, n=100, k=16, eps=1e-8):
    print(f"\nBuilding {num_patches} identical patches with n={n}, k={k}")
    print("-" * 50)

    A_blocks = []
    B_blocks = []
    patch_gaps = []

    for i in range(num_patches):
        print(f"  Patch {i+1}/{num_patches}...")

        # Fixed seed (identical patches)
        A, B, z0 = build_plaquette_patch(n=n, k=k, seed=123)

        z0 = z0 / np.linalg.norm(z0)
        P = np.eye(len(z0)) - np.outer(z0, z0)

        A_proj = P @ A @ P
        B_proj = P @ B @ P

        # Patch-level gap
        B_patch_reg = B_proj + eps * np.eye(B_proj.shape[0])
        w_patch, _ = scipy.linalg.eigh(A_proj, B_patch_reg)
        w_patch = np.sort(np.real(w_patch))

        positive_patch = w_patch[w_patch > 1e-6]
        patch_gap = float(positive_patch[0]) if len(positive_patch) > 0 else 0.0

        patch_gaps.append(patch_gap)
        print(f"    Patch gap ≈ {patch_gap:.6e}")

        A_blocks.append(A_proj)
        B_blocks.append(B_proj)

    print("\nPatch gap statistics:")
    print(f"    Mean patch gap ≈ {np.mean(patch_gaps):.6e}")
    print(f"    Min patch gap  ≈ {np.min(patch_gaps):.6e}")

    # Assemble block-diagonal matrices
    A_global = scipy.linalg.block_diag(*A_blocks)
    B_global = scipy.linalg.block_diag(*B_blocks)

    # Increased inter-patch coupling
    coupling_strength = 0.05
    block_size = A_blocks[0].shape[0]

    for i in range(num_patches - 1):
        left = i * block_size
        right = (i + 1) * block_size

        for j in range(5):
            idx_left = left + block_size - 1 - j
            idx_right = right + j

            B_global[idx_left, idx_right] -= coupling_strength
            B_global[idx_right, idx_left] -= coupling_strength

            B_global[idx_left, idx_left] += coupling_strength
            B_global[idx_right, idx_right] += coupling_strength

    print("\nSolving generalized eigenvalue problem (global)...")

    B_reg = B_global + eps * np.eye(B_global.shape[0])
    w, _ = scipy.linalg.eigh(A_global, B_reg)
    w = np.sort(np.real(w))

    positive = w[w > 1e-6]
    gap = float(positive[0]) if len(positive) > 0 else 0.0

    print(f"\nGlobal smallest positive eigenvalue (gap candidate) = {gap:.6e}")
    print(f"Eigenvalue range: [{np.min(w):.6e}, {np.max(w):.6e}]")

    return gap


if __name__ == "__main__":
    print("=" * 60)
    print("IDENTICAL PATCH GLUING TEST (stronger coupling)")
    print("=" * 60)

    configs = [
        (2, 100, 16),
        (6, 100, 16),
        (10, 100, 16),
    ]

    for num_patches, n, k in configs:
        print("\n" + "=" * 60)
        gap = global_test(
            num_patches=num_patches,
            n=n,
            k=k,
            eps=1e-8,
        )
        print(f"Config: patches={num_patches}, n={n}, k={k} → gap = {gap:.6e}")
