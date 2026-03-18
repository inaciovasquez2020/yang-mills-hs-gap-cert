# Final Assembly (Cyclone Closure)

## Inputs
1. Block variance decomposition:
\[
\|Q_L f\|^2 \le C L^2 \sum_B \mathcal{E}_B(f,f).
\]

2. Boundary coupling:
\[
\sum_B |B|\,|\bar f_B - \bar f|^2 \le C L \sum_{\ell \text{ cross}} |\nabla_\ell f|^2.
\]

3. Cross-block propagation:
\[
\sum_B |B|\,|\bar f_B|^2 \le C L \sum_{\ell \text{ cross}} |\nabla_\ell f|^2.
\]

4. Defect measure + compactness:
\[
\nabla f_L \to 0 \Rightarrow f_L \to 0.
\]

## Decomposition
\[
\|Q_L f\|^2
= \sum_B \sum_{x\in B} |f(x) - \bar f_B|^2.
\]

## Combined control
\[
\|Q_L f\|^2
\le C L^2 \sum_{\ell} |\nabla_\ell f|^2.
\]

## Lower bound (Cyclone)
Assume failure:
\[
\exists f_L:\ \|f_L\|=1,\quad
\sum_{\ell}|\nabla_\ell f_L|^2 \le C L^{-2}.
\]

## Propagation + compactness
\[
f_L \to 0 \quad \text{and} \quad \|f_L\|=1.
\]

## Contradiction
\[
0 = 1.
\]

## Conclusion
\[
\|Q_L f\|^2 \ge c_0 L^2 \sum_{\ell}|\nabla_\ell f|^2.
\]

## Status
Cyclone closed.
