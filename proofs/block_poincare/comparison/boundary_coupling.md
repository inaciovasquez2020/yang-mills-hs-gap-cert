# Boundary Coupling Between Blocks

## Interface edges
Let \(\partial(B_i,B_j)\) denote edges connecting adjacent blocks.

## Energy split
\[
\mathcal{E}_G(f,f)
= \sum_B \mathcal{E}_B(f,f) + \sum_{\partial(B_i,B_j)} |\nabla_\ell f|^2.
\]

## Boundary control
For adjacent blocks \(B_i,B_j\),
\[
|\bar f_{B_i} - \bar f_{B_j}|^2
\le C L^{-1} \sum_{\ell \in \partial(B_i,B_j)} |\nabla_\ell f|^2.
\]

## Coupled variance
\[
\sum_B |B|\,|\bar f_B - \bar f|^2
\le C L \sum_{\partial(B_i,B_j)} |\nabla_\ell f|^2.
\]

## Global control
\[
\|f - \bar f\|^2
\le C L^2 \sum_{\ell} |\nabla_\ell f|^2.
\]

## Status
Couples block averages via boundary gradients.
