import math

def tail_eta(L: float, Lambda: float, m0: float, P: int):
    r0 = (2.0*math.pi/L) * (P + 0.5)
    if r0 <= 0:
        return 0.0
    alpha = 2.0/(Lambda*Lambda)
    beta = m0*m0
    c = 2.0 * math.pi * math.pi
    term = c * math.exp(-alpha*r0*r0) / (alpha * (r0*r0 + beta)**2)
    return math.sqrt(max(0.0, term))

def tail_delta(L: float, Lambda: float, m0: float, P: int):
    r0 = (2.0*math.pi/L) * (P + 0.5)
    if r0 <= 0:
        return 0.0
    alpha = 2.0/(Lambda*Lambda)
    beta = m0*m0
    c = 2.0 * math.pi * math.pi
    term = c * math.exp(-alpha*r0*r0) / (alpha * (r0*r0 + beta)**2)
    return math.sqrt(max(0.0, term))
