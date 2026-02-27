from ym.vortex_mixing.python.noise_dobrushin import scale_influence, choose_eta

def test_scaling():
    alpha0=10.0
    eta=choose_eta(alpha0,target=0.9)
    alpha=scale_influence(alpha0,eta)
    assert alpha<1.0
