import numpy as np
from ym.vortex_mixing.python.noise_dobrushin import choose_eta, scale_influence

def test_scaling():
    alpha0 = 10.0
    target = 0.9
    eta = choose_eta(alpha0, target=target)
    expected = target / alpha0
    assert abs(eta - expected) < 1e-10, f"Expected {expected}, got {eta}"
    
    # Test original version
    degree = 4
    eta2 = choose_eta(alpha0, degree=degree)
    expected2 = alpha0 / max(1, degree)
    assert abs(eta2 - expected2) < 1e-10

def test_scale_influence():
    delta = 5.0
    degree = 3
    result = scale_influence(delta, degree)
    assert abs(result - 5.0/3.0) < 1e-10
