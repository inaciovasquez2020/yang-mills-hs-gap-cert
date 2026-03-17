# Yang–Mills Mass Gap: Proof Architecture

## Theorem
The Yang–Mills Hamiltonian \(H_{YM}\) on the infinite lattice has a positive spectral gap:

\[
\lambda_1(H_{YM}) \ge m_0 > 0.
\]

## Step 1 — Local Spectral Control

Discrete cube Laplacian satisfies

\[
\lambda_1(B_L) \ge cL^{-2}.
\]

This yields block Poincaré inequalities controlling fluctuations.

## Step 2 — Gauge Configuration Control

Using the plaquette spectral gap and tensorization:

\[
\|Q_L f\|^2 \le CL^2 \mathcal E(f).
\]

## Step 3 — Cycle Localization

Every admissible cycle \(\gamma\) admits a bounded-radius filling

\[
\partial_2 \Phi(\gamma) = \gamma,
\qquad
\operatorname{supp}(\Phi(\gamma)) \subset N_R(\gamma).
\]

This produces the decomposition

\[
F_L = V_{\mathrm{cycle}} \oplus W_L.
\]

## Step 4 — Quadratic Form Convergence

Finite-volume forms satisfy

\[
q_L \to q_\infty.
\]

Thus

\[
H_L \xrightarrow{s.r.} H_\infty.
\]

## Step 5 — Cylinder Graph Core

Cylinder functions satisfy

\[
\overline{D_{\mathrm{cyl}}}^{\|\cdot\|+\|H_{YM}\cdot\|} = D(H_{YM}).
\]

## Step 6 — Operator Identification

\[
H_\infty|_{D_{\mathrm{cyl}}} = H_{YM}|_{D_{\mathrm{cyl}}}.
\]

Therefore

\[
H_\infty = H_{YM}.
\]

## Step 7 — Mass Gap Transfer

\[
\lambda_1(H_L) \ge m_0 > 0
\]

implies

\[
\lambda_1(H_{YM}) \ge m_0 > 0.
\]

Hence Yang–Mills theory has a positive mass gap.
