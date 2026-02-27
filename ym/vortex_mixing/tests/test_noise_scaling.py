import numpy as np
from ym.vortex_mixing.python.noise_dobrushin import influence_scale, choose_eta

def test_influence_scale_basic():
    alpha0 = 10.0
    eta = 0.49
    alpha = influence_scale(alpha0, eta)
    assert abs(alpha - alpha0 * eta) < 1e-10
    assert alpha < 5.0  # 10 * 0.49 = 4.9 < 5

def test_choose_eta():
    alpha0 = 5.0
    target = 0.9
    eta = choose_eta(alpha0, target=target)
    expected = target / alpha0
    assert abs(eta - expected) < 1e-10
    assert 0 < eta < 1

def test_scaling_relation():
    # Test consistency: influence_scale(alpha0, choose_eta(alpha0, target)) ≈ target
    alpha0 = 7.5
    target = 0.85
    eta = choose_eta(alpha0, target=target)
    alpha = influence_scale(alpha0, eta)
    assert abs(alpha - target) < 1e-10
