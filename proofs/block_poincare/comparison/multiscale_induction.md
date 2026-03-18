# Multiscale Induction on Block Size

## Scale sequence
Let \(L_k = 2^k\).

## Inductive hypothesis
\[
\|Q_{L_k} f\|^2 \le C L_k^2 \sum_{\ell} |\nabla_\ell f|^2.
\]

## Decomposition
\[
Q_{L_{k+1}} = Q_{L_k} + (P_{L_k} - P_{L_{k+1}}).
\]

## Orthogonality
\[
\|Q_{L_{k+1}} f\|^2
\le 2\|Q_{L_k} f\|^2 + 2\|(P_{L_k} - P_{L_{k+1}})f\|^2.
\]

## Block refinement bound
\[
\|(P_{L_k} - P_{L_{k+1}})f\|^2
\le C L_k^2 \sum_{\ell} |\nabla_\ell f|^2.
\]

## Inductive step
\[
\|Q_{L_{k+1}} f\|^2 \le C L_{k+1}^2 \sum_{\ell} |\nabla_\ell f|^2.
\]

## Status
Reduces global inequality to base-scale control.
