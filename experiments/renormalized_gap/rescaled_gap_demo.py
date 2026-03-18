def m_L(L,kappa=1,c=1):
    return kappa*c/(L**2)

def rescaled_gap(L,kappa=1,c=1):
    return L**2*m_L(L,kappa,c)

for L in [4,6,8,10,12,16,20]:
    print("L",L,"rescaled_gap",rescaled_gap(L))
