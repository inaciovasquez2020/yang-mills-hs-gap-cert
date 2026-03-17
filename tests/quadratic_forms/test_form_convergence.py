import numpy as np

def q(L, f):
    A = np.diag([1.0 + 1.0/L, 2.0 + 1.0/L, 3.0 + 1.0/L])
    return float(f @ A @ f)

def q_inf(f):
    A = np.diag([1.0, 2.0, 3.0])
    return float(f @ A @ f)

def test_form_convergence():
    f = np.array([1.0, -2.0, 0.5])
    errs = [abs(q(L, f) - q_inf(f)) for L in [10, 20, 40, 80, 160]]
    assert errs[-1] < errs[0]
    assert errs[-1] < 0.05

if __name__ == "__main__":
    test_form_convergence()
    print("quadratic form convergence test: PASS")
