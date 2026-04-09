# YM-4 — Continuum transfer

## Status
OPEN

## Target
Prove that the lattice lower bound survives the continuum and infinite-volume limit.

## Required objects
1. Lattice spacing family \(a \downarrow 0\).
2. Finite-volume family \(\Lambda_L \uparrow \mathbb{R}^d\).
3. Lattice operators \(H_{a,L}\) or coercive forms \(q_{a,L}\).
4. Uniform lower bound
   \[
   q_{a,L}(\phi) \ge m_\ast \|\phi\|^2
   \]
   with \(m_\ast > 0\) independent of \(a,L\).
5. Continuum limiting Hilbert space / quadratic-form domain.
6. Limit operator \(H\) or limit form \(q\).

## Proof shell
- Define the directed family \((a,L)\).
- State the uniform lattice coercivity bound.
- Prove tightness / compactness of the family of forms or semigroups.
- Identify the continuum limit object.
- Prove lower-semicontinuity of the quadratic form under the limit.
- Transfer the bound
  \[
  q(\phi) \ge m_\ast \|\phi\|^2
  \]
  to the limit object.
- Pass from finite volume to infinite volume.
- Conclude persistence of a strictly positive spectral gap in the limit.

## Blocking lemma
Uniform coercivity is stable under the joint continuum and thermodynamic limit.
