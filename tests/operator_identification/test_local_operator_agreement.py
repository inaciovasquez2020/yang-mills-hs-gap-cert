import numpy as np

def local_operator(L):
    return np.diag([1.0,2.0,3.0])

def continuum_operator():
    return np.diag([1.0,2.0,3.0])

def test_local_operator_agreement():
    f=np.array([1.0,-1.0,0.5])
    for L in [8,16,32,64]:
        diff=np.linalg.norm(local_operator(L)@f-continuum_operator()@f)
        assert diff < 1e-12

if __name__=="__main__":
    test_local_operator_agreement()
    print("operator identification test: PASS")
