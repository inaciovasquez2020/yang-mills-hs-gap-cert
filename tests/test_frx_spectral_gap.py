import numpy as np
from ym.frx.toy_confining import lazy_uniform_kernel

def test_lazy_uniform_second_eigenvalue():
    for m in [4, 7, 16]:
        for alpha in [0.1, 0.25, 0.6]:
            P = lazy_uniform_kernel(m, alpha)
            w = np.linalg.eigvals(P)
            w = np.array(sorted(w, key=lambda z: -abs(z)))
            lam1 = w[0]
            lam2 = w[1]
            assert abs(lam1 - 1.0) < 1e-10
            assert abs(abs(lam2) - (1.0 - alpha)) < 1e-8
