import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh


# ============================================================
# Random SU(2) configuration
# ============================================================

def random_su2():
    a = np.random.normal(size=4)
    a /= np.linalg.norm(a)
    a0, a1, a2, a3 = a
    return np.array([
        [a0 + 1j * a3,  a2 + 1j * a1],
        [-a2 + 1j * a1, a0 - 1j * a3]
    ], dtype=np.complex128)


def make_random_U(L, seed=None):
    if seed is not None:
        np.random.seed(seed)
    U = np.empty((L, L, L, L, 4, 2, 2), dtype=np.complex128)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    for mu in range(4):
                        U[x, y, z, t, mu] = random_su2()
    return U


# ============================================================
# Blocking (simple averaging placeholder)
# ============================================================

def block_weighted_covariant_4d(U, L, b, beta, alpha_override=0.0):
    Lc = L // b
    Uc = np.empty((Lc, Lc, Lc, Lc, 4, 2, 2), dtype=np.complex128)

    for x in range(Lc):
        for y in range(Lc):
            for z in range(Lc):
                for t in range(Lc):
                    for mu in range(4):
                        block = []
                        for dx in range(b):
                            for dy in range(b):
                                for dz in range(b):
                                    for dt in range(b):
                                        block.append(
                                            U[b*x+dx, b*y+dy, b*z+dz, b*t+dt, mu]
                                        )
                        avg = sum(block) / len(block)
                        # reunitarize
                        u, s, vh = np.linalg.svd(avg)
                        Uc[x, y, z, t, mu] = u @ vh

    return Uc


# ============================================================
# Sparse Laplacian construction
# ============================================================

def build_W_from_links(U, L, kappa=1.0):
    N = L ** 4

    rows = []
    cols = []
    data = []

    def idx(x, y, z, t):
        return ((t * L + z) * L + y) * L + x

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):

                    i = idx(x, y, z, t)

                    for mu, (dx, dy, dz, dt) in enumerate([
                        (1,0,0,0),
                        (0,1,0,0),
                        (0,0,1,0),
                        (0,0,0,1),
                    ]):

                        xn = (x + dx) % L
                        yn = (y + dy) % L
                        zn = (z + dz) % L
                        tn = (t + dt) % L

                        j = idx(xn, yn, zn, tn)

                        Ulink = U[x, y, z, t, mu]
                        w = kappa * np.real(np.trace(Ulink)) / 2.0

                        # off-diagonal
                        rows.append(i); cols.append(j); data.append(-w)
                        rows.append(j); cols.append(i); data.append(-w)

                        # diagonal
                        rows.append(i); cols.append(i); data.append(w)
                        rows.append(j); cols.append(j); data.append(w)

    return coo_matrix((data, (rows, cols)), shape=(N, N)).tocsr()


# ============================================================
# Sparse Laplacian gap
# ============================================================

def laplacian_gap(W, tol=1e-10, maxiter=2000):

    vals = eigsh(
        W,
        k=3,
        which="SM",
        tol=tol,
        maxiter=maxiter,
        return_eigenvectors=False
    )

    vals = np.sort(np.real(vals))

    for v in vals:
        if v > 1e-12:
            return float(v)

    return float(vals[-1])


# ============================================================
# CLI entry
# ============================================================

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--lattice", type=int, default=8)
    parser.add_argument("--blocking", type=int, default=2)
    parser.add_argument("--beta", type=float, default=2.3)
    parser.add_argument("--sweeps", type=int, default=0)
    parser.add_argument("--kappa", type=float, default=1.0)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()

    L = args.lattice
    b = args.blocking

    U = make_random_U(L, seed=args.seed)

    Wf = build_W_from_links(U, L, kappa=args.kappa)
    gap_f = laplacian_gap(Wf)

    Uc = block_weighted_covariant_4d(U, L, b, args.beta)
    Wc = build_W_from_links(Uc, L//b, kappa=args.kappa)
    gap_c = laplacian_gap(Wc)

    print("fine_gap", gap_f)
    print("coarse_gap", gap_c)
