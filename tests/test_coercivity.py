import numpy as np
import pytest
from scipy.linalg import eigh

@pytest.fixture
def H():
    """Sample Hessian matrix"""
    return np.array([[2.0, -1.0, 0.0],
                     [-1.0, 2.0, -1.0],
                     [0.0, -1.0, 2.0]])

@pytest.fixture
def K():
    """Sample stiffness matrix"""
    return np.array([[1.0, 0.0, 0.0],
                     [0.0, 1.0, 0.0],
                     [0.0, 0.0, 1.0]])

def test_coercivity(H, K, tol=1e-10):
    """Test coercivity condition H - μK ≥ 0"""
    eigvals = eigh(H, K, eigvals_only=True)
    mu_min = np.min(eigvals)
    
    print(f"Minimum generalized eigenvalue: {mu_min:.6f}")
    print(f"All eigenvalues: {eigvals}")
    
    assert mu_min > -tol, f"Coercivity failed: μ_min = {mu_min}"
    # Explicitly return None to avoid warning
    return None
