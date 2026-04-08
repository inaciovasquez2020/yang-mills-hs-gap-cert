# WTR Refined Coercive Contraction

## Corrected status

The following is a conditional closure statement, not an unconditional proof of the Yang--Mills mass gap.

## Hypotheses

Let \(B\) be a block of sidelength \(L\), let \(U\) be a background connection, and let
\[
\mathcal A := \left\{ U \in \mathcal U :
\sup_{Q \subset B} \|F_U\|_{L^2(Q)}^2 < \epsilon_0 L^{-2}
\right\}.
\]

Let \(f \in (\ker \Delta_B)^\perp\) satisfy the chosen gauge-fixing condition, and assume the Hessian admits the decomposition
\[
\nabla^2 S_B(U) = \beta \Delta_B + \mathcal R(F_U)
\]
on the gauge-fixed sector, where \(\mathcal R(F_U)\) is symmetric on that sector.

Assume further that:

1. **Block spectral gap**
\[
\langle f,\Delta_B f\rangle \ge \lambda_1(\Delta_B)\|f\|_{L^2}^2,
\qquad
\lambda_1(\Delta_B) \ge c_\Delta L^{-2},
\qquad
f \in (\ker \Delta_B)^\perp.
\]

2. **Remainder domination**
\[
|\langle f,\mathcal R(F_U)f\rangle|
\le C\,\epsilon_0\,L^{-2}\,\|f\|_{L^2}^2
\qquad
(\forall\,U\in\mathcal A).
\]

3. **Strict smallness**
\[
C\,\epsilon_0 < \beta\,c_\Delta.
\]

## Energy identification

Define
\[
E_{\mathrm{main}}(f) := \beta \langle f,\Delta_B f\rangle,
\qquad
E_{\mathrm{gain}}(f) := |\langle f,\mathcal R(F_U)f\rangle|.
\]

Then
\[
\langle f,\nabla^2 S_B(U)f\rangle
=
E_{\mathrm{main}}(f)+\langle f,\mathcal R(F_U)f\rangle.
\]

## Contractive bound

From the hypotheses,
\[
E_{\mathrm{gain}}(f)
\le C\,\epsilon_0\,L^{-2}\|f\|_{L^2}^2
\le \frac{C\,\epsilon_0}{c_\Delta}\,\langle f,\Delta_B f\rangle
=
\frac{C\,\epsilon_0}{\beta c_\Delta}\,E_{\mathrm{main}}(f).
\]

Set
\[
\eta := 1 - \frac{C\,\epsilon_0}{\beta c_\Delta}.
\]
By strict smallness,
\[
\eta>0.
\]
Hence
\[
E_{\mathrm{gain}}(f)\le (1-\eta)\,E_{\mathrm{main}}(f).
\]

Therefore
\[
\langle f,\nabla^2 S_B(U)f\rangle
\ge \eta\,E_{\mathrm{main}}(f)
= \eta\beta \langle f,\Delta_B f\rangle
\ge \eta\beta c_\Delta L^{-2}\|f\|_{L^2}^2.
\]

## Corrected conclusion

Under the three hypotheses above, the RPD error-gain contraction holds on the admissible sector \(\mathcal A\), and the blocked two-bubble mechanism is excluded inside that sector.

This yields a conditional coercivity-transfer statement on \(\mathcal A\). It does not by itself constitute an unconditional proof of the Yang--Mills mass gap.

## Remaining unconditional gap

To upgrade this note from conditional to unconditional, it remains to prove theorem-level statements for:

\[
\lambda_1(\Delta_B) \ge c_\Delta L^{-2},
\]
\[
|\langle f,\mathcal R(F_U)f\rangle|
\le C\,\epsilon_0\,L^{-2}\,\|f\|_{L^2}^2,
\]
uniformly on the actual operator/data path and gauge-fixed admissible sector.
