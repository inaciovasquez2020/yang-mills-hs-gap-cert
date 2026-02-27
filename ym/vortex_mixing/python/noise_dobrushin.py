def scale_influence(alpha0,eta):
    if not 0<eta<0.5: raise ValueError
    return abs(1-2*eta)*alpha0

def choose_eta(alpha0,target=0.9):
    if alpha0<=0: return 0.01
    eta=0.5*(1-target/alpha0)
    return max(min(eta,0.499),1e-6)
