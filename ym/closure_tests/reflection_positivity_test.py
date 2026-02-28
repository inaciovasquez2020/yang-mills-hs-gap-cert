import numpy as np


def matrix_psd(M, tol=1e-8):
    """
    Helper: check if matrix M is positive semidefinite.
    Not a pytest test (does not start with 'test_').
    """
    M = np.asarray(M)
    if M.ndim != 2 or M.shape[0] != M.shape[1]:
        return False
    vals = np.linalg.eigvalsh(M)
    return np.all(vals >= -tol)


def test_matrix_psd_basic():
    """Simple sanity check."""
    M = np.eye(4)
    assert matrix_psd(M)
