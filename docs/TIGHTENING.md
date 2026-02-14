Tightening the HS-Gap Certificates

Purpose
Replace placeholder kernel/projector inputs with analytic Hilbert–Schmidt
upper bounds derived from heat-kernel regularization and transverse projection.

Method
Analytic decay bounds are evaluated as functions of (L, Λ):
- η from heat-kernel smoothing
- δ from projector–Hessian commutator suppression

These bounds are conservative upper limits and preserve correctness
of the inequality η + δ < 1.

Status
- Analytic bounds are active
- CI continues to enforce the same invariants
- Certificates remain valid and monotone

Future Work
Exact kernel evaluation can replace analytic bounds without
changing the certification framework.

Refinement v2: Explicit Fourier-mode HS evaluation
The HS components are computed as truncated lattice sums over (2π/L)Z^4 up to |n_i|≤P with a continuous tail bound.
Certificates record P in params and CI recomputes eta,delta deterministically.

