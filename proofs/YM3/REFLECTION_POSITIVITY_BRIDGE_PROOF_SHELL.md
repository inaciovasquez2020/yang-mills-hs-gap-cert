# YM-3 — Reflection positivity bridge

## Status
OPEN

## Target
Derive the positivity/coercivity statement from a bona fide Yang-Mills reflection positivity or transfer-matrix argument.

## Required objects
1. Euclidean lattice Yang-Mills measure.
2. Reflection operator \(\Theta\).
3. Positive-time algebra \(\mathcal A_+\).
4. Reflection-positive form
   \[
   \langle F, F \rangle_{\Theta} := \mathbb E\!\left[\overline{\Theta F}\,F\right].
   \]
5. Transfer/semigroup operator inducing the physical Hamiltonian.

## Proof shell
- Define the reflection \(\Theta\) on lattice observables.
- Define the positive-time observable algebra \(\mathcal A_+\).
- Prove reflection positivity:
  \[
  \mathbb E\!\left[\overline{\Theta F}\,F\right] \ge 0
  \quad\text{for all }F \in \mathcal A_+.
  \]
- Construct the induced physical Hilbert space.
- Identify the transfer operator or generator.
- Connect the induced generator to the coercive quadratic form on the physical quotient.
- State the bridge from reflection positivity to the spectral lower bound.

## Blocking lemma
Construction of the physical Hamiltonian/coercive form from the reflection-positive Yang-Mills measure.
