import numpy as np

def orthogonal_projection(n, k, seed=0):
    rng = np.random.default_rng(seed)
    A = rng.normal(size=(n, k))
    Q, _ = np.linalg.qr(A)
    return Q @ Q.T

def operator_norm(P):
    w = np.linalg.eigvalsh(P)
    return float(np.max(np.abs(w)))

def test_projection_operator_norm_is_one():
    for k in [2, 4, 8, 16]:
        P = orthogonal_projection(100, k, seed=k)
        assert abs(operator_norm(P) - 1.0) < 1e-10

if __name__ == "__main__":
    test_projection_operator_norm_is_one()
    print("projection stability test: PASS")
