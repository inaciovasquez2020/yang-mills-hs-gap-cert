import numpy as np
from numpy.linalg import eigvalsh

np.random.seed(42)  # Fixed seed for reproducibility

print("Testing Hessian lower bound scaling with L")

for L in [4, 8, 16, 32]:
    N = L**4
    beta = 2.0  # Fixed coupling
    
    def random_field():
        return np.random.randn(N)
    
    def grad_action(phi):
        # Fixed: added * operator between 2 and beta
        return 2.0 * beta * (2.0*phi - np.roll(phi,1) - np.roll(phi,-1))
    
    samples = 100
    ratios = []
    
    for _ in range(samples):
        phi = random_field()
        g = grad_action(phi)
        # Compute Rayleigh quotient: <φ, Hφ>/<φ,φ> where H is Hessian
        # For quadratic action S = β∑(∇φ)², Hessian = 2β(-∇²)
        # So <φ, Hφ> = 2β ∑ (∇φ)² = 2β <g,g>? Actually g = Hessian * φ
        # Better: compute <φ, Hessian φ> directly
        hessian_phi = grad_action(phi)  # This is actually Hessian * φ for quadratic action
        rayleigh = np.dot(phi.ravel(), hessian_phi.ravel()) / np.dot(phi.ravel(), phi.ravel())
        ratios.append(rayleigh)
    
    print(f"L = {L:3d}, N = {N:6d}, mean λ_min ≈ {np.mean(ratios):.6f}, std = {np.std(ratios):.6f}")
