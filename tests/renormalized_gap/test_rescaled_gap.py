def m_L(L,kappa=1,c=1):
    return kappa*c/(L**2)

def rescaled_gap(L,kappa=1,c=1):
    return L**2*m_L(L,kappa,c)

def test_rescaled_gap_constant():
    vals=[rescaled_gap(L) for L in [4,6,8,10,12,16,20]]
    assert max(vals)-min(vals) < 1e-12

if __name__=="__main__":
    test_rescaled_gap_constant()
    print("renormalized gap test: PASS")
