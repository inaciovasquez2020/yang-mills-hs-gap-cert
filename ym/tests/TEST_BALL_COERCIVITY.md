Object:
Covariant Laplacian Δ_A on B_R with Dirichlet boundary conditions,
restricted to physical (Gauss-law satisfying) fields.

Test inequality:
<φ, (-Δ_A) φ> ≥ m_loc ||φ||^2
for all φ ⟂ ker(Δ_A), supp φ ⊂ B_R.

Procedure:
- Fix gauge (Coulomb).
- Compute lowest Dirichlet eigenvalue λ_1(A,R).
- Check inf_R inf_A λ_1(A,R) > 0.
If λ_1(A,R) → 0 as R → ∞, record explicit approximate zero-modes.
