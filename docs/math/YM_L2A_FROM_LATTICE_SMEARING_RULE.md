# L2a from the Lattice Smearing Rule

## Status

Conditional.

## Target

\[
\mathbf{(L2a)}\quad
\phi(f)=\sum_{x\in\Lambda_n}\langle K_{n,f}(x),U_x\rangle.
\]

## Weakest sufficient micro-fix

Assume the finite-volume smeared field is defined by a lattice smearing rule of the form
\[
\phi(f):=\sum_{x\in\Lambda_n}\langle W_n f(x),U_x\rangle,
\]
where
\[
W_n:\mathcal S(\mathbb R^4,\mathfrak g)\to \mathfrak g^{\Lambda_n}
\]
is a linear discretization operator.

Define
\[
K_{n,f}(x):=(W_n f)(x).
\]

Then immediately
\[
\phi(f)=\sum_{x\in\Lambda_n}\langle K_{n,f}(x),U_x\rangle.
\]

Moreover, linearity of \(W_n\) gives
\[
K_{n,\alpha f+\beta g}(x)=\alpha K_{n,f}(x)+\beta K_{n,g}(x).
\]

## Reduction lock

\[
\text{explicit lattice smearing rule}
\Longrightarrow
\mathbf{(L2a)}.
\]

## Next admissible micro-fix

\[
\boxed{\text{prove }
\sum_{x\in\Lambda_n}|(W_n f)(x)|^2\le C\|f\|_{\mathcal S,m}^2}
\]
