import numpy as np

def local_operator(L, m=6):
    diag = np.array([1.0 + (j + 1) / L for j in range(m)])
    return np.diag(diag)

def q_L(L, f):
    A = local_operator(L, len(f))
    return float(f @ A @ f)

def q_inf(f):
    A = np.diag(np.ones(len(f)))
    return float(f @ A @ f)

def test_pointwise_form_convergence_on_finite_vectors():
    vectors = [
        np.array([1.0, 0.0, 0.0, 0.0]),
        np.array([1.0, -1.0, 0.5, 0.0]),
        np.array([0.0, 1.0, -2.0, 1.0]),
    ]
    for f in vectors:
        errs = [abs(q_L(L, f) - q_inf(f)) for L in [10, 20, 40, 80, 160]]
        assert errs[-1] < errs[0]
        assert errs[-1] < 0.1

def test_uniform_form_bound_on_finite_vectors():
    vectors = [
        np.array([1.0, 0.0, 0.0, 0.0]),
        np.array([1.0, -1.0, 0.5, 0.0]),
        np.array([0.0, 1.0, -2.0, 1.0]),
    ]
    for f in vectors:
        vals = [q_L(L, f) for L in [10, 20, 40, 80, 160]]
        assert max(vals) < 20.0

if __name__ == "__main__":
    test_pointwise_form_convergence_on_finite_vectors()
    test_uniform_form_bound_on_finite_vectors()
    print("common core tests: PASS")
