# RPD Closure Chain (2026-04)

## Status
This note is non-claiming.
It records the next admissible RPD closure chain only.

## Authoritative upstream status
- Negative Result Certified
- Conditional Reduction Framework
- Open Core Lemma

## Core RPD quantity
\[
E_B(U;f):=\langle f,(\nabla^2 S_B(U)-\beta\Delta_B)f\rangle.
\]

## Cell decomposition target
\[
E_B(U;f)=\sum_Q E_Q(U;f).
\]

## Local estimate target
\[
|E_Q(U;f)|\le C\bigl(L^{-2}\|f\|_Q^2+L^{-1}\|\nabla_B f\|_Q^2\bigr).
\]

## Missing gain lemma
\[
\sum_Q \|\nabla_B f\|_Q^2 \le C_{\mathrm{gain}} L^{-1}\|f\|^2,
\qquad
f\in(\ker\Delta_B)^\perp.
\]

## Consequence
If the gain lemma holds, then
\[
|E_B(U;f)|\le C' L^{-2}\|f\|^2,
\quad
C' := C(1+C_{\mathrm{gain}}).
\]

Hence
\[
\langle f,\nabla^2 S_B(U)f\rangle
\ge
\beta\langle f,\Delta_B f\rangle - C' L^{-2}\|f\|^2.
\]

If
\[
\lambda_1(\Delta_B)\ge c_\Delta L^{-2}
\]
and
\[
\beta c_\Delta > C',
\]
then
\[
\gamma_B \ge (\beta c_\Delta - C')L^{-2}.
\]

## Registry map
- RPD-4 := kernel preservation under blocking
- RPD-5a := pulse_logbound_implies_lambdaMin_zero
- RPD-5b := pulse_logbound_implies_noncoercive_target
- RPD-6 := two_bubble_log_locality_incompatible

## Non-claim
This file does not upgrade repository status.
It records theorem targets and the exact missing lemma only.
