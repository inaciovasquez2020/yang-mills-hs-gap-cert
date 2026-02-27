import numpy as np
from two_plaquette_model import build_two_patch

def orth_basis_from_P(P, tol=1e-10):
    """Extract orthonormal basis from projector P"""
    n = P.shape[0]
    # Get eigenvectors with eigenvalues close to 1
    eigvals, eigvecs = np.linalg.eigh(P)
    mask = eigvals > 1 - tol
    Q = eigvecs[:, mask]
    return Q

def single_C1(Aform, Bform, P0, tol=1e-10):
    """Compute optimal C1 for given matrices and projector"""
    # Get basis for subspace orthogonal to zero mode
    Q = orth_basis_from_P(P0, tol)
    
    if Q.shape[1] == 0:
        return 0.0  # No degrees of freedom left
    
    # Project matrices
    A = Q.T @ Aform @ Q
    B = Q.T @ Bform @ Q
    
    # Ensure symmetry
    A = 0.5 * (A + A.T)
    B = 0.5 * (B + B.T)
    
    # Check if B is positive definite
    eigB = np.linalg.eigvalsh(B)
    if np.min(eigB) <= tol:
        # Regularize
        B = B + tol * np.eye(B.shape[0])
    
    # Solve M = B^{-1} A
    try:
        M = np.linalg.solve(B, A)
    except np.linalg.LinAlgError:
        # Use pseudoinverse if singular
        B_pinv = np.linalg.pinv(B)
        M = B_pinv @ A
    
    M = 0.5 * (M + M.T)
    
    # Maximum eigenvalue gives C1 bound
    eigM = np.linalg.eigvalsh(M)
    return float(np.max(eigM))

def proj_zero_mode(z0, tol=1e-10):
    """Projector orthogonal to zero mode"""
    n = len(z0)
    z0_norm = z0 / (np.sqrt(np.sum(z0**2)) + tol)
    return np.eye(n) - np.outer(z0_norm, z0_norm)

def grid_search(n=700, k=24, seed=0, C2max=20.0, m=101):
    """Search for optimal C2 that minimizes C1"""
    print(f"\n{'='*60}")
    print(f"Two-Plaquette Fit: n={n}, k={k}, seed={seed}")
    print(f"{'='*60}")
    
    # Build system
    print("Building two-patch configuration...")
    Aform, Bform, z0 = build_two_patch(n=n, k=k, seed=seed)
    print(f"Matrix dimensions: {Aform.shape}")
    
    # Project out zero mode
    P0 = proj_zero_mode(z0)
    
    # Test without perturbation (C2=0)
    print("\nTesting unperturbed system (C2=0)...")
    C1_0 = single_C1(Aform, Bform, P0)
    print(f"C1(0) = {C1_0:.6f}")
    
    # Search over C2
    bestC1 = C1_0
    bestC2 = 0.0
    C2_vals = np.linspace(0.0, C2max, m)
    
    print(f"\nSearching over {m} C2 values from 0 to {C2max}")
    print("-" * 50)
    
    for i, C2 in enumerate(C2_vals):
        if i % 20 == 0:
            print(f"Progress: {i}/{m}")
        
        # Modified operator: H = Aform + C2 * Bform
        A_pert = Aform + C2 * Bform
        C1 = single_C1(A_pert, Bform, P0)
        
        if C1 < bestC1:
            bestC1 = C1
            bestC2 = C2
            print(f"  New best: C1={C1:.6f}, C2={C2:.2f}")
    
    print("\n" + "="*60)
    print(f"OPTIMAL: C2 = {bestC2:.6f}, C1 = {bestC1:.6f}")
    print("="*60)
    
    return bestC1, bestC2

if __name__ == "__main__":
    # Test with smaller parameters first
    C1, C2 = grid_search(n=400, k=24, seed=0, C2max=20.0, m=51)
