# Cross-Block Propagation of Fluctuations

## Block graph
Let \(\mathcal{B}_L\) be the adjacency graph of \(L\)-blocks.

## Block averages
\[
m_B := \frac{1}{|B|}\sum_{x\in B} f(x).
\]

## Orthogonality
\[
\sum_B |B|\, m_B = 0.
\]

## Propagation energy
\[
\sum_{(B,B')\in E(\mathcal{B}_L)} |m_B - m_{B'}|^2
\le C L^{-1} \sum_{\ell \in \partial(B,B')} |\nabla_\ell f|^2.
\]

## Block-graph Poincaré
\[
\sum_B |B|\,|m_B|^2
\le C L^2 \sum_{(B,B')\in E(\mathcal{B}_L)} |m_B - m_{B'}|^2.
\]

## Combined bound
\[
\sum_B |B|\,|m_B|^2
\le C L \sum_{\ell \text{ crossing blocks}} |\nabla_\ell f|^2.
\]

## Consequence
Block-average fluctuations cannot localize independently.

## Status
Cross-block propagation closes the remaining localization channel.
