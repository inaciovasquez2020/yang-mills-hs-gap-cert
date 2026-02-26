from tests.spectral_wall.spectral_form_lower_bound import rayleigh_quotient

def test_rayleigh_form_positive():
    for k in [1, 2, 3]:
        for ell in [0, 1, 2, 3]:
            q = rayleigh_quotient(d=4, k=k, ell=ell)
            assert q > 1.0
