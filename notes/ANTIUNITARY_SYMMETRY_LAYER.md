# Antiunitary Symmetry Layer

Let \(\mathcal H\) be a complex Hilbert space and \(H\) a self-adjoint Hamiltonian.

## Definition
An operator \(A:\mathcal H\to\mathcal H\) is an admissible anti-symmetry iff
\[
A(\alpha\psi+\beta\phi)=\overline{\alpha}\,A\psi+\overline{\beta}\,A\phi
\]
and
\[
\langle A\psi,A\phi\rangle=\overline{\langle \psi,\phi\rangle}
\]
for all \(\alpha,\beta\in\mathbb C\), \(\psi,\phi\in\mathcal H\), and
\[
AHA^{-1}=H.
\]

## Consequences
\[
AH=HA
\]
and
\[
A e^{-itH} A^{-1}=e^{itH}.
\]

If \(O=O^\ast\) and \(AOA^{-1}=O\), then
\[
\langle A\psi,O\,A\psi\rangle=\langle \psi,O\psi\rangle.
\]

## Placement
Use only in complex-Hilbert/operator symmetry layers.
Do not use in FO^k, EF-game, or \(\mathbb F_2\)-cycle-space layers.
