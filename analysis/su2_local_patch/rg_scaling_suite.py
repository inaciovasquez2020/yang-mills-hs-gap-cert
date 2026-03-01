import numpy as np

from analysis.su2_local_patch.metropolis_su2_4d import (
    build_su2_lattice,
    thermalize_metropolis,
)

from analysis.su2_local_patch.laplacian_gap_after_blocking import (
    build_W_from_links,
    laplacian_gap,
)


def block_links_average(U, L, b):
    """
    Very simple blocking: average links over b^4 hypercubes.
    Produces coarse link field with size Lc = L // b.
    """

    assert L % b == 0
    Lc = L // b

    Uc = np.zeros((Lc, Lc, Lc, Lc, 4, 2, 2), dtype=np.complex128)

    for xc in range(Lc):
        for yc in range(Lc):
            for zc in range(Lc):
                for tc in range(Lc):
                    for mu in range(4):

                        acc = np.zeros((2, 2), dtype=np.complex128)

                        for dx in range(b):
                            for dy in range(b):
                                for dz in range(b):
                                    for dt in range(b):
                                        x = xc * b + dx
                                        y = yc * b + dy
                                        z = zc * b + dz
                                        t = tc * b + dt
                                        acc += U[x, y, z, t, mu]

                        acc /= (b ** 4)

                        # crude projection back to SU(2)
                        u, s, vh = np.linalg.svd(acc)
                        Uc[xc, yc, zc, tc, mu] = u @ vh

    return Uc, Lc


def one_seed(L, b, beta, sweeps, eps, kappa, seed, alpha_override=None):
    """
    Run single-seed RG gamma experiment.
    alpha_override is accepted for test compatibility.
    """

    U = build_su2_lattice(L, seed=seed)

    U = thermalize_metropolis(
        U,
        L,
        beta,
        sweeps=sweeps,
        eps=eps,
        seed=seed,
    )

    W_fine = build_W_from_links(U, L, kappa=kappa)
    fine_gap = laplacian_gap(W_fine)

    Uc, Lc = block_links_average(U, L, b)

    W_coarse = build_W_from_links(Uc, Lc, kappa=kappa)
    coarse_gap = laplacian_gap(W_coarse)

    if fine_gap <= 0:
        gamma = np.nan
    else:
        # Correct Laplacian RG normalization
        gamma = coarse_gap / (b * b * fine_gap)
    return {
        "fine_gap": float(fine_gap),
        "coarse_gap": float(coarse_gap),
        "gamma": float(gamma),
    }


def aggregate(rows):
    """
    Aggregate list of row dictionaries returned by one_seed.
    Must match test expectations.
    """

    fine = np.array([r["fine_gap"] for r in rows])
    coarse = np.array([r["coarse_gap"] for r in rows])
    gamma = np.array([r["gamma"] for r in rows])

    return {
        "fine_gap": {
            "mean": float(fine.mean()),
            "std": float(fine.std()),
        },
        "coarse_gap": {
            "mean": float(coarse.mean()),
            "std": float(coarse.std()),
        },
        "gamma_lap": {
            "mean": float(gamma.mean()),
            "std": float(gamma.std()),
        },
        "n": len(rows),
    }
