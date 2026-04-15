# Block Spectral Gap Next Missing Object (2026-04)

Status: OPEN

## Immediate target
Prove the canonical open core lemma
\[
\gamma_B \ge c L^{-2}.
\]

## Equivalent form
\[
\sup_U \left\|\nabla^2 S_B(U)-\beta \Delta_B\right\| \le C L^{-2}.
\]

## Discharge routes
1. Direct proof of `BLOCK_SPECTRAL_GAP_CORE_LEMMA`.
2. Full discharged sublemma ladder plus explicit composition:
   - Sublemma 1 — Local Hessian Approximation
   - Sublemma 2 — Local-to-Global Laplacian Comparison
   - Sublemma 3 — Spectral Transfer

## Required output
1. Canonical theorem statement.
2. Equivalent operator-norm form.
3. Explicit direct-proof route.
4. Explicit sublemma-ladder route.
5. Composition rule from the three sublemmas to the core lemma.
6. Exact interface to `SPECTRAL_CONTRACTION_RG`.

## Upgrade rule
No claim upgrade is permitted from this file alone.
