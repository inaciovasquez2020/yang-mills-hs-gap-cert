import numpy as np


def idx(x, y, z, t, L):
    return ((x * L + y) * L + z) * L + t


def shift(coord, mu, step, L):
    c = list(coord)
    c[mu] = (c[mu] + step) % L
    return tuple(c)


def su2_proj(M):
    U, _, Vh = np.linalg.svd(M)
    U2 = U @ Vh
    if np.linalg.det(U2) < 0:
        U2[:, 0] *= -1
    return U2


def block_weighted_covariant_4d(U, L, b, beta):
    if L % b != 0:
        raise ValueError("L must be divisible by b")
    if b <= 0:
        raise ValueError("b must be positive")

    Lc = L // b
    Uc = np.zeros((Lc**4, 4, 2, 2), dtype=np.complex128)

    alpha = 0.65 * beta - 0.15 * np.log(b)
    alpha = max(float(alpha), 0.0)

    for sc in range(Lc**4):
        xc = sc // (Lc**3)
        rc = sc - xc * (Lc**3)
        yc = rc // (Lc**2)
        rc = rc - yc * (Lc**2)
        zc = rc // Lc
        tc = rc - zc * Lc

        x0, y0, z0, t0 = xc * b, yc * b, zc * b, tc * b

        for mu in range(4):
            M = np.zeros((2, 2), dtype=np.complex128)
            total_w = 0.0

            x_end, y_end, z_end, t_end = shift((x0, y0, z0, t0), mu, b, L)

            for k in range(b):
                xf = (x0 + (k if mu == 0 else 0)) % L
                yf = (y0 + (k if mu == 1 else 0)) % L
                zf = (z0 + (k if mu == 2 else 0)) % L
                tf = (t0 + (k if mu == 3 else 0)) % L

                Uf = U[idx(xf, yf, zf, tf, L), mu]

                xe, ye, ze, te = shift((xf, yf, zf, tf), mu, +1, L)

                Pto = path_to_4d(U, L, (x0, y0, z0, t0), (xf, yf, zf, tf))
                Pbk = path_to_4d(U, L, (xe, ye, ze, te), (x_end, y_end, z_end, t_end))

                dist = abs(k - (b - 1) / 2.0)
                w = np.exp(-alpha * dist)

                M += w * (Pto @ Uf @ Pbk)
                total_w += w

            Uc[sc, mu] = su2_proj(M / total_w)

    return Uc


def path_to_4d(U, L, start, end):
    P = np.eye(2, dtype=np.complex128)
    curr = [int(start[0]), int(start[1]), int(start[2]), int(start[3])]
    end = (int(end[0]), int(end[1]), int(end[2]), int(end[3]))

    for mu in range(4):
        steps = (end[mu] - curr[mu]) % L
        for _ in range(steps):
            P = P @ U[idx(curr[0], curr[1], curr[2], curr[3], L), mu]
            curr[mu] = (curr[mu] + 1) % L

    return P
