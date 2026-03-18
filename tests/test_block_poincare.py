import numpy as np
from experiments.block_eigenvalue_computation import compute_block_eigenvalues

def test_minimal_eigenvalue_positive():
    lambdas = compute_block_eigenvalues(L=4)
    assert np.min(lambdas) > 0

