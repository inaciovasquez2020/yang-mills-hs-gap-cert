# RPD Targets (2026-04)

## Non-claim
This file records theorem targets only.
No proof claim is made here.

## RPD-4
Kernel preservation under blocking:
\[
\ker \nabla^2 S_B(U)=\mathcal B(\ker \nabla^2 S(U))
\]
modulo the normalized gauge/null sector.

## RPD-5a
Pulse-to-Rayleigh transfer:
\[
\text{pulse/log-growth lower bound}
\Longrightarrow
\lambda_{\min}\!\left(\nabla^2 S_B(U)\mid(\ker\Delta_B)^\perp\right)=0.
\]

## RPD-5b
Zero bottom mode implies noncoercive target:
\[
\lambda_{\min}\!\left(\nabla^2 S_B(U)\mid(\ker\Delta_B)^\perp\right)=0
\Longrightarrow
\text{noncoercive target}.
\]

## RPD-6
Two-bubble incompatibility:
\[
\text{two separated pulse carriers}
\Longrightarrow
\text{failure of uniform block coercivity}.
\]

## RPD Error Gain Lemma
\[
\sum_Q \|\nabla_B f\|_Q^2 \le C_{\mathrm{gain}}L^{-1}\|f\|^2
\qquad
f\in(\ker\Delta_B)^\perp.
\]

## RPD Gap Chain
If
\[
|E_Q(U;f)|\le C\bigl(L^{-2}\|f\|_Q^2+L^{-1}\|\nabla_B f\|_Q^2\bigr),
\]
then the Error Gain Lemma implies
\[
|E_B(U;f)|\le C' L^{-2}\|f\|^2.
\]
Hence
\[
\lambda_{\min}\!\left(\nabla^2 S_B(U)\mid(\ker\Delta_B)^\perp\right)
\ge
\beta\lambda_1(\Delta_B)-C' L^{-2}.
\]
If
\[
\lambda_1(\Delta_B)\ge c_\Delta L^{-2}
\quad\text{and}\quad
\beta c_\Delta>C',
\]
then
\[
\gamma_B\ge (\beta c_\Delta-C')L^{-2}.
\]
