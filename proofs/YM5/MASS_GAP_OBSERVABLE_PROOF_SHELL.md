# YM-5 — Mass-gap observable

## Status
OPEN

## Target
Identify a gauge-invariant correlator/observable whose decay is forced by the coercive lower bound.

## Required objects
1. Physical Hilbert space \(\mathcal H_{\mathrm{phys}}\).
2. Positive Hamiltonian \(H\) with lower bound \(H \ge m_\ast > 0\) on the non-vacuum sector.
3. Vacuum vector \(\Omega\).
4. Gauge-invariant observable \(O\) with \(\langle \Omega, O \Omega \rangle = 0\).
5. Two-point function
   \[
   C(t) := \langle \Omega, O^\ast e^{-tH} O \Omega \rangle .
   \]

## Proof shell
- Define the gauge-invariant observable \(O\).
- Prove \(O\Omega\) lies in the physical non-vacuum sector.
- Apply the spectral lower bound
  \[
  H \ge m_\ast
  \quad\text{on}\quad
  (\mathbb C \Omega)^\perp .
  \]
- Derive exponential decay
  \[
  C(t) \le e^{-m_\ast t}\|O\Omega\|^2 .
  \]
- Interpret \(m_\ast\) as the mass gap seen by the observable.
- State the observable-level mass-gap conclusion.

## Blocking lemma
A nontrivial gauge-invariant observable exists whose vacuum-subtracted two-point function detects the physical spectral gap.
