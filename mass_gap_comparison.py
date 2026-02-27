import numpy as np
import matplotlib.pyplot as plt

def laplacian_min(L):
    """Minimum positive eigenvalue of 1D Laplacian"""
    k = 2 * np.pi / L
    return 2 * (1 - np.cos(k))

def hessian_min(L, mass):
    """Minimum eigenvalue of Hessian with mass term"""
    return mass + laplacian_min(L)

L_values = [4, 6, 8, 10, 16, 32, 64, 128, 256]
mass = 8.0

print("Comparison: Laplacian vs Hessian with mass")
print("="*60)
print(f"{'L':>4} {'Laplacian λ_min':>16} {'× L²':>10} {'Hessian λ_min':>16} {'Asymptotic':>12}")
print("-"*60)

for L in L_values:
    lap = laplacian_min(L)
    hess = hessian_min(L, mass)
    print(f"{L:4d} {lap:16.8f} {lap*L*L:10.4f} {hess:16.8f} {hess:12.4f}")

# Show that with mass, λ_min → mass as L→∞
print("\n" + "="*60)
print("CRITICAL OBSERVATION:")
print("="*60)
print("""
Without mass term: λ_min ∝ 1/L² → 0 as L → ∞
With mass term m²: λ_min → m² as L → ∞

The Wilson action generates a mass term m² = 8β(a) from the constant term
in its quadratic expansion. This provides the uniform lower bound needed
for the Bakry-Émery curvature condition.
""")
