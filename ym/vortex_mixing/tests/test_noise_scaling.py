from ym.vortex_mixing.python.noise_dobrushin import influence_scale, choose_eta

def test_influence_scale_basic():
    alpha0 = 10.0
    eta = 0.49
    alpha = influence_scale(alpha0, eta)
    assert alpha < 1.0

def test_choose_eta():
    alpha0 = 5.0
    eta = choose_eta(alpha0, target=0.9)
    alpha = influence_scale(alpha0, eta)
    assert alpha < 0.91
