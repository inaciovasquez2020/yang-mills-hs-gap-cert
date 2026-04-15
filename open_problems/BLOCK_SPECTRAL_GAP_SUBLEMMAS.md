# Block Spectral Gap Sublemma Ladder

Status: OPEN

Target:
Reduce `BLOCK_SPECTRAL_GAP_CORE_LEMMA` to the following strictly weaker explicit sublemmas.

## Sublemma 1 — Local Hessian Approximation
For each block \(B\) of side length \(L\),
\[
\sup_{U \in \mathcal U_{\mathrm{adm}}(B)}
\left\|
\nabla^2 S_B(U)-\beta \Delta_B^{\mathrm{loc}}
\right\|
\le C_1 L^{-2}.
\]

## Sublemma 2 — Local-to-Global Laplacian Comparison
\[
\left\|
\Delta_B^{\mathrm{loc}}-\Delta_B
\right\|
\le C_2 L^{-2}.
\]

## Sublemma 3 — Spectral Transfer
If
\[
\left\|
\nabla^2 S_B(U)-\beta \Delta_B
\right\|
\le C L^{-2}
\]
uniformly in \(U\), then
\[
\gamma_B \ge c L^{-2}.
\]

Reduction rule:
No claim upgrade is permitted unless either the core lemma is discharged or every sublemma above is discharged and their composition is written explicitly.
