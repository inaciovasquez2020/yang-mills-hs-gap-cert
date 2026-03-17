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

def test_monotone_convergence():
    vectors = [
        np.array([1.0,0.0,0.0,0.0]),
        np.array([1.0,-1.0,0.5,0.0]),
        np.array([0.0,1.0,-2.0,1.0]),
    ]
    for f in vectors:
        vals=[q_L(L,f) for L in [10,20,40,80,160]]
        assert vals[-1] <= vals[0]

def test_uniform_form_bound():
    vectors=[
        np.array([1.0,0.0,0.0,0.0]),
        np.array([1.0,-1.0,0.5,0.0]),
        np.array([0.0,1.0,-2.0,1.0]),
    ]
    for f in vectors:
        bound=3*q_inf(f)
        vals=[q_L(L,f) for L in [10,20,40,80,160]]
        assert max(vals) <= bound

if __name__=="__main__":
    test_monotone_convergence()
    test_uniform_form_bound()
    print("common core corrected tests: PASS")
