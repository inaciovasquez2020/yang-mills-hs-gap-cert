import numpy as np
from experiments/global_overlap_correction import compute_overlap_factor

def test_mass_gap_bound_positive():
    alpha = compute_overlap_factor(L=4)
    assert alpha > 0

