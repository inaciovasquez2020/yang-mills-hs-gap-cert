def influence_scale(alpha0: float, eta: float) -> float:
    if not (0.0 < eta < 0.5):
        raise ValueError("eta must be in (0, 1/2)")
    return abs(1.0 - 2.0*eta) * alpha0

def choose_eta(alpha0: float, target: float = 0.99) -> float:
    if alpha0 <= 0:
        return 0.01
    if alpha0 < 1:
        return 0.01
    eta = 0.5 * (1.0 - target/alpha0)
    if eta <= 0.0:
        eta = 1e-6
    if eta >= 0.499:
        eta = 0.499
    return eta
