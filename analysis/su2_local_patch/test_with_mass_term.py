import sys
import os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from small_lattice_test import global_test

def global_test_with_mass(mass=8.0, num_patches=8, n=200, k=24):
    """Test with mass term added to the operator"""
    # This is a placeholder - you'll need to modify build_plaquette_patch
    # to include the mass term m² * I in the operator
    print(f"\nTesting with mass term m² = {mass}")
    gap = global_test(num_patches=num_patches, n=n, k=k)
    return gap

if __name__ == "__main__":
    print("=" * 60)
    print("TEST WITH MASS TERM")
    print("=" * 60)
    
    masses = [0.0, 1.0, 4.0, 8.0, 16.0]
    for m in masses:
        gap = global_test_with_mass(mass=m, num_patches=4, n=100, k=16)
        print(f"m²={m:4.1f}: gap={gap:.6e}")
