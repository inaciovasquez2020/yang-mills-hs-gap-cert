import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigsh


def site_index(x, y, z, t, L):
    return ((t * L + z) * L + y) * L + x


def build_W_from_links(U, L, kappa=1.0):
    """
    Build sparse weighted graph Laplacian from SU(2) link variables.

    U is assumed to have shape:
        (L, L, L, L, 4, 2, 2)

    We construct a scalar weight Laplacian using
    w = kappa * Re Tr(U_mu(x)) / 2
    """

    N = L ** 4

    rows = []
    cols = []
    data = []

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    i = site_index(x, y, z, t, L)

                    for mu, (dx, dy, dz, dt) in enumerate([
                        (1, 0, 0, 0),
                        (0, 1, 0, 0),
                        (0, 0, 1, 0),
                        (0, 0, 0, 1),
                    ]):
                        xn = (x + dx) % L
                        yn = (y + dy) % L
                        zn = (z + dz) % L
                        tn = (t + dt) % L

                        j = site_index(xn, yn, zn, tn, L)

                        Ulink = U[x, y, z, t, mu]
                        w = kappa * np.real(np.trace(Ulink)) / 2.0

                        # Off-diagonal entries
                        rows.append(i)
                        cols.append(j)
                        data.append(-w)

                        rows.append(j)
                        cols.append(i)
                        data.append(-w)

                        # Diagonal contributions
                        rows.append(i)
                        cols.append(i)
                        data.append(w)

                        rows.append(j)
                        cols.append(j)
                        data.append(w)

    W = coo_matrix((data, (rows, cols)), shape=(N, N)).tocsr()
    return W


def laplacian_gap(W, tol=1e-10, maxiter=2000):
    """
    Compute smallest nonzero eigenvalue of Laplacian.
    Works for sparse CSR matrix.
    """

    # Compute smallest few eigenvalues
    vals = eigsh(
        W,
        k=3,
        which="SM",
        tol=tol,
        maxiter=maxiter,
        return_eigenvectors=False,
    )

    vals = np.sort(np.real(vals))

    for v in vals:
        if v > 1e-12:
            return float(v)

    return float(vals[-1])


if __name__ == "__main__":
    print("Sparse Laplacian module loaded.")
