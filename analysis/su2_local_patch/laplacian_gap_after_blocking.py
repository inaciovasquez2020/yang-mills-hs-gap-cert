import numpy as np
import scipy.sparse as sp
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh
from scipy.sparse.linalg._eigen.arpack.arpack import ArpackNoConvergence


# ============================================================
# SU(2) random configuration
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
# Blocking (simple covariant averaging + reunitarization)
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
                        u, s, vh = np.linalg.svd(avg)
                        Uc[x, y, z, t, mu] = u @ vh

    return Uc


# ============================================================
# Sparse Laplacian
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

                        rows.append(i); cols.append(j); data.append(-w)
                        rows.append(j); cols.append(i); data.append(-w)

                        rows.append(i); cols.append(i); data.append(w)
                        rows.append(j); cols.append(j); data.append(w)

    W = coo_matrix((data, (rows, cols)), shape=(N, N)).tocsr()

    # enforce symmetry explicitly
    W = (W + W.T) * 0.5

    if np.iscomplexobj(W.data):
        W.data = np.real(W.data)

    return W


# ============================================================
# Robust smallest nonzero eigenvalue
# ============================================================

def laplacian_gap(W, tol=1e-8, maxiter=20000):

    # Attempt 1: direct smallest magnitude
    try:
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
    except ArpackNoConvergence:
        pass

    # Attempt 2: shift-invert near zero
    for sigma in (0.0, 1e-6, 1e-5, 1e-4):
        try:
            vals = eigsh(
                W,
                k=3,
                sigma=sigma,
                which="LM",
                tol=tol,
                maxiter=maxiter,
                return_eigenvectors=False
            )
            vals = np.sort(np.real(vals))
            for v in vals:
                if v > 1e-12:
                    return float(v)
            return float(vals[-1])
        except Exception:
            continue

    # Attempt 3: increase k
    vals = eigsh(
        W,
        k=8,
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
# CLI
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
