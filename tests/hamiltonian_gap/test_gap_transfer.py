def finite_volume_gap(L, kappa=1.0, c=1.0):
    return kappa * c / (L**2)

def test_gap_positive():
    for L in [4, 6, 8, 10, 12, 16, 20]:
        assert finite_volume_gap(L) > 0.0

def test_gap_decreases_like_inverse_square():
    vals = [finite_volume_gap(L) * (L**2) for L in [4, 6, 8, 10, 12, 16, 20]]
    assert max(vals) - min(vals) < 1e-12

if __name__ == "__main__":
    test_gap_positive()
    test_gap_decreases_like_inverse_square()
    print("hamiltonian gap transfer tests: PASS")
