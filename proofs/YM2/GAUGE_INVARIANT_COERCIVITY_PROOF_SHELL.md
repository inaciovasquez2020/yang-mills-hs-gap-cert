# YM-2 — Gauge-invariant coercivity

## Status
OPEN

## Target
Prove a uniform strictly positive lower bound on the physical quotient after removal of gauge zero modes.

## Required objects
1. Background configuration \(U_\ast\).
2. Hessian/Wilson operator \(\Lambda_{U_\ast}\).
3. Gauge-kernel subspace \(K_{\mathrm{gauge}}\).
4. Physical quotient \(Q = \mathrm{Dom}(\Lambda_{U_\ast}) / K_{\mathrm{gauge}}\).
5. Coercive constant \(\lambda_\ast > 0\).

## Proof shell
- Define the gauge kernel.
- Prove \(\Lambda_{U_\ast}\) descends to the quotient \(Q\).
- Define the quotient quadratic form.
- Prove non-negativity on \(Q\).
- Upgrade non-negativity to strict positivity.
- State the uniform lower bound
  \[
  \langle \phi, \Lambda_{U_\ast}\phi\rangle \ge \lambda_\ast \|\phi\|^2
  \quad\text{for all nonzero }[\phi]\in Q.
  \]

## Blocking lemma
Conditional: Every zero mode of the descended quadratic form on the quotient \(Q\) is gauge-induced, so the induced operator on \(Q\) has strictly positive bottom spectrum.
No non-gauge zero mode survives in the physical quotient.
