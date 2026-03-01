import numpy as np


def idx(x, y, z, t, L):
    return ((t % L) * L + (z % L)) * L * L + (y % L) * L + (x % L)


def _get_link(U, x, y, z, t, mu, L):
    return U[x % L, y % L, z % L, t % L, mu]


def build_W_from_links(U, L, kappa=1.0):
    """
    Build nearest-neighbor Laplacian matrix from SU(2) link field.
    """

    N = L ** 4
    W = np.zeros((N, N), dtype=np.float64)

    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):

                    i = idx(x, y, z, t, L)
                    W[i, i] = 8.0 * kappa

                    for mu in range(4):
                        xp = (x + (mu == 0)) % L
                        yp = (y + (mu == 1)) % L
                        zp = (z + (mu == 2)) % L
                        tp = (t + (mu == 3)) % L

                        j = idx(xp, yp, zp, tp, L)

                        W[i, j] -= kappa
                        W[j, i] -= kappa

    return W


def laplacian_gap(W, tol=1e-8, maxiter=20000):
    """
    Return smallest positive eigenvalue (gap).
    Removes trivial zero mode.
    """

    w = np.linalg.eigvalsh(W)

    # remove zero modes
    w = w[w > tol]

    if len(w) == 0:
        return 0.0

    return float(w.min())
