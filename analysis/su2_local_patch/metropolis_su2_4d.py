import numpy as np


def idx(x, y, z, t, L):
    return ((t % L) * L + (z % L)) * L * L + (y % L) * L + (x % L)


def random_su2(rng):
    a = rng.normal(size=4)
    a /= np.linalg.norm(a)
    a0, a1, a2, a3 = a
    return np.array(
        [
            [a0 + 1j * a3, a2 + 1j * a1],
            [-a2 + 1j * a1, a0 - 1j * a3],
        ],
        dtype=np.complex128,
    )


def su2_inv(U):
    return U.conj().T


def shift4(x, y, z, t, mu, step, L):
    if mu == 0:
        return ((x + step) % L, y, z, t)
    if mu == 1:
        return (x, (y + step) % L, z, t)
    if mu == 2:
        return (x, y, (z + step) % L, t)
    if mu == 3:
        return (x, y, z, (t + step) % L)


def make_random_U(L, seed=None):
    rng = np.random.default_rng(seed)
    U = np.zeros((L, L, L, L, 4, 2, 2), dtype=np.complex128)
    for x in range(L):
        for y in range(L):
            for z in range(L):
                for t in range(L):
                    for mu in range(4):
                        U[x, y, z, t, mu] = random_su2(rng)
    return U


def build_su2_lattice(L, seed=None):
    return make_random_U(L, seed=seed)


def staple(U, L, x, y, z, t, mu):
    S = np.zeros((2, 2), dtype=np.complex128)

    for nu in range(4):
        if nu == mu:
            continue

        x1 = shift4(x, y, z, t, nu, +1, L)
        x2 = shift4(x, y, z, t, mu, +1, L)

        U_nu = U[x, y, z, t, nu]
        U_mu_shift = U[x1[0], x1[1], x1[2], x1[3], mu]
        U_nu_inv = su2_inv(U[x2[0], x2[1], x2[2], x2[3], nu])

        S += U_nu @ U_mu_shift @ U_nu_inv

    return S


def local_action_term(U_mu, S, beta):
    return -beta * np.real(np.trace(U_mu @ S))


def propose_su2(rng, eps):
    dU = random_su2(rng)
    return dU


def thermalize_metropolis(U, L, beta, sweeps=10, eps=0.25, seed=0):
    rng = np.random.default_rng(seed)

    for _ in range(sweeps):
        for x in range(L):
            for y in range(L):
                for z in range(L):
                    for t in range(L):
                        for mu in range(4):

                            S = staple(U, L, x, y, z, t, mu)

                            U_old = U[x, y, z, t, mu]
                            U_prop = propose_su2(rng, eps) @ U_old

                            dS = (
                                local_action_term(U_prop, S, beta)
                                - local_action_term(U_old, S, beta)
                            )

                            if dS < 0 or rng.random() < np.exp(-dS):
                                U[x, y, z, t, mu] = U_prop

    return U
