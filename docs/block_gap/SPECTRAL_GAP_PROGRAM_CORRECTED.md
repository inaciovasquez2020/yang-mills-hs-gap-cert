# Spectral Gap Program: Corrected Conditional Treatment

## Setup

Let
\[
S(U)
=
\beta \sum_{p \subset \Lambda_L}\bigl(1-\operatorname{Re}\operatorname{Tr}(U_p)\bigr).
\]

Partition plaquettes into
\[
P(\Lambda_L)=P_{\partial}\sqcup P_{\circ},
\]
where \(P_{\partial}\) are plaquettes touching \(\partial\Lambda_L\), and \(P_{\circ}\) are interior plaquettes. Define
\[
S_{\partial}(U):=\beta\sum_{p\in P_{\partial}}\bigl(1-\operatorname{Re}\operatorname{Tr}(U_p)\bigr),
\qquad
S_{\circ}(U):=\beta\sum_{p\in P_{\circ}}\bigl(1-\operatorname{Re}\operatorname{Tr}(U_p)\bigr).
\]
Then
\[
S=S_{\partial}+S_{\circ}.
\]

## Step 1 — Correct Hessian Statement

The Hessian splits:
\[
\nabla^2 S=\nabla^2 S_{\partial}+\nabla^2 S_{\circ}.
\]

However,
\[
\nabla^2 S_{\circ}\big|_{E_{\partial}}\neq 0
\]
in general, because interior plaquettes adjacent to the boundary may contain boundary links, creating mixed derivatives. Thus the identity
\[
\lambda_{\min}(\nabla^2 S|_{E_{\partial}})
=
\lambda_{\min}(\nabla^2 S_{\partial}|_{E_{\partial}})
\]
is not justified without additional control.

## Step 2 — Uniform Operator Bound

For each plaquette \(p\),
\[
\sup_U \bigl\|\nabla^2 (1-\operatorname{Re}\operatorname{Tr}(U_p))\bigr\|_{\mathrm{op}}
\le C_p
\]
for a constant depending only on the compact gauge group. Hence
\[
\|\nabla^2 S_{\partial}(U)\|_{\mathrm{op}}
\le C_0 \beta |P_{\partial}|
\asymp C_0 \beta L^{d-1}.
\]

This is an upper bound only. It does not imply coercivity.

## Step 3 — Conditional Coercive Decomposition

Assume the existence of a decomposition
\[
\nabla^2 S_{\partial}(U)=\beta H_{\partial}^{(2)}+\mathcal R_{\partial}(U),
\]
with
\[
H_{\partial}^{(2)} \succeq c_0 \Pi_{\partial},
\qquad
\|\mathcal R_{\partial}(U)\|_{\mathrm{op}}\le C_1
\]
uniformly in \(U\), where \(\Pi_{\partial}\) projects onto the relevant gauge-fixed boundary directions.

Then
\[
\nabla^2 S_{\partial}(U)
\succeq
(\beta c_0-C_1)\Pi_{\partial}.
\]

Under the scale transfer
\[
A=L\,\widetilde A
\quad\Longrightarrow\quad
\nabla_A^2 = L^{-2}\nabla_{\widetilde A}^2,
\]
this yields
\[
\nabla_A^2 S_{\partial}(U)\succeq c\,L^{-2}\Pi_{\partial}
\]
provided \(\beta c_0>C_1\).

## Step 4 — Conditional Brascamp–Lieb Step

Assume the gauge-fixed block measure is log-concave with Hessian lower bound
\[
\nabla^2 V(U)\succeq c\,L^{-2} I.
\]

Then Brascamp–Lieb gives
\[
\operatorname{Var}_{\mu}(f)
\le
c^{-1}L^2\,\mathbb E_{\mu}\|\nabla f\|^2.
\]

Equivalently,
\[
\mathrm{gap}(\mathcal L)\ge c\,L^{-2}.
\]

## Step 5 — Correct Conditional Conclusion

Therefore, conditional on:

1. gauge fixing producing a valid finite-dimensional coordinate system,
2. mixed-derivative control from \(S_{\circ}\),
3. a uniform remainder bound \(\|\mathcal R_{\partial}(U)\|_{\mathrm{op}}\le C_1\),
4. log-concavity / Brascamp–Lieb applicability for the gauge-fixed measure,
5. extension from boundary coercivity to full block coercivity,

one obtains
\[
\mathrm{gap}(\mathcal L_B)\ge c\,L^{-2}.
\]

## Corrected Status

The argument is not rigorous as written without the five conditional ingredients above.

What is established:
\[
S=S_{\partial}+S_{\circ},
\qquad
\|\nabla^2 S_{\partial}(U)\|_{\mathrm{op}}\lesssim \beta L^{d-1}.
\]

What remains open:
\[
\inf_U \lambda_{\min}(\nabla^2 S_B(U))\ge cL^{-2}.
\]

This is still the core missing lemma.

