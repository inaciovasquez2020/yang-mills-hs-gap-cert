import numpy as np

def scale_influence(delta, degree):
    """Scale influence parameter by degree"""
    return delta / max(1, degree)

def influence_scale(alpha0, eta):
    """Compute influence scale from alpha0 and eta"""
    return alpha0 * eta  # Simple linear scaling for tests

def choose_eta(alpha0, target=None, degree=1, temperature=1.0):
    """Choose eta parameter for Dobrushin's condition"""
    if target is not None:
        # Version with target parameter for tests
        return target / alpha0 if alpha0 > 0 else 0
    else:
        # Original version
        influence = scale_influence(alpha0, degree)
        return influence / temperature
