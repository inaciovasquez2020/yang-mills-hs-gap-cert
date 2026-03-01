# Spectral Domination Closure — Stress Test Counterexamples (Spec)

## Objective
Attempt to falsify the closure chain by constructing mechanisms that can produce near-zero excitations
without violating the stated finite-volume electric coercivity inputs.

## M1. Boundary/Edge Mode Mechanism (BC-driven)
### Failure mode
If boundary links do not carry the full electric term in H_Λ, boundary rotations can become low-energy:
  E_{∂Λ} not included ⇒ boundary soft modes.
### Required invariant to rule out
(BC-COVER) Every boundary link term appears in the electric part:
  E_Λ^2 = Σ_{links in Λ} Δ_link   (no boundary omission).

## M2. Gauss-constraint kernel enlargement
### Failure mode
If the "projection used in GOR" is not exactly P_{ker H_Λ}, then the Casimir gap is to the wrong subspace:
  ker(E_Λ^2 | H_phys) may be larger than vacuum.
### Required invariant to rule out
(KER-ID) Identify P0 precisely and prove:
  ker(E_Λ^2 | H_phys) ∩ (P0^⊥) has spectrum ≥ c_G.

## M3. Large-field thin-tube states
### Failure mode
States supported on a small set where plaquettes are far from identity but V_Λ small due to trace effects.
### Required invariant to rule out
(BARRIER) There exists neighborhood N(I) and c0>0 such that:
  U_p ∉ N(I) ⇒ 1 - ReTr(U_p) ≥ c0
uniform in Λ, p.

## M4. Continuum scaling mismatch
### Failure mode
Coefficient mismatch in H_a can invalidate asymptotic comparisons.
### Required invariant to rule out
(SCALE-MAP) Record exact scaling:
  H_{a,Λ} = (g(a)^2/(2a)) Σ E^2 + (1/(2g(a)^2 a)) Σ (2 - ReTr U_p)
and verify all manuscript steps use the same normalization.

## Acceptance criteria (closure survives)
All of BC-COVER, KER-ID, BARRIER, SCALE-MAP are stated in repo with explicit constants or explicit
dependencies and no volume-dependent leakage.

## Pointers
- manuscripts/spectral_domination/gauge_orbit_rigidity_target.tex
- manuscripts/spectral_domination/finite_volume_domination_target.tex
- manuscripts/spectral_domination/boundary_electric_control_lemma.tex
- manuscripts/spectral_domination/uniform_spectral_domination_theorem.tex
