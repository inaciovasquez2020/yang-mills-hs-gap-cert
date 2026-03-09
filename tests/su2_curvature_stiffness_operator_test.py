import numpy as np

def su2_random():
    a = np.random.randn(4)
    a = a / np.linalg.norm(a)
    w, x, y, z = a
    return np.array([
        [w + 1j*z, x + 1j*y],
        [-x + 1j*y, w - 1j*z]
    ], dtype=complex)

def su2_dagger(U):
    return np.conjugate(U.T)

def wilson_plaquette(U1, U2, U3, U4):
    P = U1 @ U2 @ su2_dagger(U3) @ su2_dagger(U4)
    tr = np.trace(P)
    return 1.0 - np.real(tr) / 2.0

def run():
    np.random.seed(1)

    samples = 200
    energies = []

    for _ in range(samples):
        U1 = su2_random()
        U2 = su2_random()
        U3 = su2_random()
        U4 = su2_random()

        e = wilson_plaquette(U1, U2, U3, U4)
        energies.append(e)

    energies = np.array(energies)

    print("plaquette curvature statistics")
    print("min:", energies.min())
    print("mean:", energies.mean())
    print("max:", energies.max())

if __name__ == "__main__":
    run()
