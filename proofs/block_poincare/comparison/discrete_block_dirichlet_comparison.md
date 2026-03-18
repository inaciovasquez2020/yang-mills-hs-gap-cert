# Discrete Block Dirichlet Comparison

## Block decomposition
Partition the graph into blocks \(B\) of side length \(L\).
For each block define the block average
\[
(P_L f)|_B := \frac{1}{|B|}\sum_{x\in B} f(x).
\]
Set
\[
Q_L f := f - P_L f.
\]

## Local block energy
For each block \(B\), define
\[
\mathcal{E}_B(f,f) := \sum_{\ell \subset B} |\nabla_\ell f|^2.
\]

## Global energy
\[
\mathcal{E}_G(f,f) := \sum_{\ell} |\nabla_\ell f|^2.
\]

## Target comparison
Prove
\[
\|Q_L f\|^2 \le C L^2 \sum_B \mathcal{E}_B(f,f).
\]

## Equivalent lower form
\[
\sum_B \mathcal{E}_B(f,f) \ge c L^{-2}\|Q_L f\|^2.
\]

## Reduction target
Combine with
\[
\sum_B \mathcal{E}_B(f,f) \le \mathcal{E}_G(f,f)
\]
to obtain
\[
\|Q_L f\|^2 \le C L^2 \mathcal{E}_G(f,f).
\]

## Status
This is the discrete blockwise Poincare step.
