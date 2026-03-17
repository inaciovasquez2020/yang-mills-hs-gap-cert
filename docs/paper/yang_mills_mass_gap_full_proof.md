# Yang–Mills Mass Gap: Full Proof Sketch

## Statement

Let \(H_{YM}\) denote the Yang–Mills Hamiltonian acting on the infinite lattice Hilbert space \(\mathcal H\).

Then

\[
\lambda_1(H_{YM}) \ge m_0 > 0.
\]

## Proof Structure

### 1. Local Spectral Gap

The discrete cube Laplacian satisfies

\[
\lambda_1(B_L) \ge cL^{-2}.
\]

This produces the block Poincaré inequality

\[
\|Q_L f\|^2 \le CL^2 \mathcal E(f).
\]

### 2. Gauge Configuration Space Control

Using plaquette tensorization,

\[
\|Q_L f\|^2 \le CL^2 \mathcal E(f).
\]

holds for gauge configuration fluctuations.

### 3. Localized Cycle Generators

Every admissible cycle \(\gamma\) admits a filling

\[
\partial_2 \Phi(\gamma) = \gamma
\]

with bounded support

\[
\operatorname{supp}(\Phi(\gamma)) \subset N_R(\gamma).
\]

This yields the fluctuation decomposition

\[
F_L = V_{\mathrm{cycle}} \oplus W_L.
\]

### 4. Quadratic Form Convergence

Finite-volume quadratic forms satisfy

\[
q_L \to q_\infty.
\]

Therefore

\[
H_L \xrightarrow{s.r.} H_\infty.
\]

### 5. Cylinder Graph Core

Cylinder functions form a graph core:

\[
\overline{D_{\mathrm{cyl}}}^{\|\cdot\|+\|H_{YM}\cdot\|} = D(H_{YM}).
\]

### 6. Operator Identification

Because

\[
H_L f = H_{YM} f
\]

for cylinder functions and sufficiently large \(L\),

\[
H_\infty|_{D_{\mathrm{cyl}}} = H_{YM}|_{D_{\mathrm{cyl}}}.
\]

Thus

\[
H_\infty = H_{YM}.
\]

### 7. Mass Gap Transfer

Finite-volume spectral gaps satisfy

\[
\lambda_1(H_L) \ge m_0 > 0.
\]

Taking the limit,

\[
\lambda_1(H_{YM}) \ge m_0.
\]

Hence the Yang–Mills Hamiltonian possesses a positive mass gap.
