def test_chain_bound():
    R = 4
    L = 1
    k = 5
    assert k <= (R//L) + 1
