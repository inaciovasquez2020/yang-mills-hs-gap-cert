import math

def lattice_momenta_4d(L: float, P: int):
    two_pi_over_L = 2.0 * math.pi / L
    for n0 in range(-P, P+1):
        for n1 in range(-P, P+1):
            for n2 in range(-P, P+1):
                for n3 in range(-P, P+1):
                    p0 = two_pi_over_L * n0
                    p1 = two_pi_over_L * n1
                    p2 = two_pi_over_L * n2
                    p3 = two_pi_over_L * n3
                    yield (p0,p1,p2,p3)

def p2(p):
    return p[0]*p[0]+p[1]*p[1]+p[2]*p[2]+p[3]*p[3]

def heat_cutoff(p_sq: float, Lambda: float):
    return math.exp(-p_sq/(Lambda*Lambda))

def free_prop(p_sq: float, m0: float):
    return 1.0/(p_sq + m0*m0)

def hs_sum_eta(L: float, Lambda: float, m0: float, P: int):
    s = 0.0
    for p in lattice_momenta_4d(L,P):
        psq = p2(p)
        c = heat_cutoff(psq, Lambda)
        g = free_prop(psq, m0)
        a = c * g
        s += (a*a)
    return math.sqrt(s)

def hs_sum_delta(L: float, Lambda: float, m0: float, P: int):
    s = 0.0
    for p in lattice_momenta_4d(L,P):
        psq = p2(p)
        c = heat_cutoff(psq, Lambda)
        g = free_prop(psq, m0)
        b = c * g * (psq/(psq + 1.0))
        s += (b*b)
    return math.sqrt(s)
