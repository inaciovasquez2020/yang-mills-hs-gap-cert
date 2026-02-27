import numpy as np
from .transfer_matrix import row_stochasticize

def lazy_uniform_kernel(m: int, alpha: float) -> np.ndarray:
    if m <= 1:
        raise ValueError("m must be >= 2")
    if not (0.0 < alpha < 1.0):
        raise ValueError("alpha must be in (0,1)")
    I = np.eye(m)
    U = np.ones((m, m)) / m
    P = (1.0 - alpha) * I + alpha * U
    return row_stochasticize(P)
