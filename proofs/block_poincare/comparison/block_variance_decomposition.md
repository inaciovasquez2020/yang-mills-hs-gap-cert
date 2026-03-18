# Block Variance Decomposition

## Decomposition
\[
\|Q_L f\|^2 = \sum_{B} \sum_{x\in B} |f(x) - \bar f_B|^2,
\quad
\bar f_B := \frac{1}{|B|}\sum_{x\in B} f(x).
\]

## Path representation
For each \(x\in B\), fix a path \(\gamma_x\) to a reference point \(x_B\in B\).
\[
f(x) - \bar f_B
= \frac{1}{|B|}\sum_{y\in B} (f(x)-f(y))
= \frac{1}{|B|}\sum_{y\in B} \sum_{\ell\in \gamma_{x,y}} \nabla_\ell f.
\]

## Cauchy bound
\[
|f(x) - \bar f_B|^2
\le C L \sum_{\ell \subset B} |\nabla_\ell f|^2.
\]

## Summation
\[
\sum_{x\in B} |f(x) - \bar f_B|^2
\le C L^2 \sum_{\ell \subset B} |\nabla_\ell f|^2.
\]

## Global bound
\[
\|Q_L f\|^2 \le C L^2 \sum_B \sum_{\ell \subset B} |\nabla_\ell f|^2.
\]

## Status
Variance decomposition reduces block fluctuations to edge gradients.
