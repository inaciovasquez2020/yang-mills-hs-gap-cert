# Lower Bound Strategy (Cyclone)

## Target
\[
\|Q_L f\|^2 \ge c_0 L^2 \sum_{\ell}|\nabla_\ell f|^2.
\]

## Variational form
\[
\inf_{f \perp \operatorname{im}(P_L)}
\frac{\|Q_L f\|^2}{\sum_{\ell}|\nabla_\ell f|^2}
\ge c_0 L^2.
\]

## Spectral formulation
\[
\lambda_{\min}(Q_L^*Q_L \,|\, \ker P_L^\perp)
\ge c_0 L^2 \lambda_{\min}(-\Delta_G).
\]

## Obstruction
Blockwise localization:
\[
f = \sum_B f_B,\quad \text{supp}(f_B)\subset B.
\]

## Required exclusion
\[
\|Q_L f\|^2 \not\ll L^2 \sum_{\ell}|\nabla_\ell f|^2
\quad \text{for all localized } f.
\]

## Strategy
1. Prove non-existence of near-kernel localized modes.
2. Establish uniform spectral gap for \(Q_L\) on orthogonal complement.
3. Enforce cross-block propagation of fluctuations.

## Status
Cyclone formulated as spectral exclusion principle.
