# Exact Kernel/Overlap Target for the Chosen \(W_n\)

## Status

Conditional.

## Current micro-frontier

Identify the exact kernel/overlap hypotheses satisfied by the chosen discretization operator
\[
W_n:\mathcal S(\mathbb R^4,\mathfrak g)\to \ell^2(\Lambda_n;\mathfrak g).
\]

## Weakest sufficient formulation

Assume there exist kernels \(\eta_{n,x}\) such that
\[
(W_n f)(x)=a_n^{4/2}\int_{\mathbb R^4}\eta_{n,x}(y)f(y)\,dy.
\]

The exact hypotheses needed are:

\[
\mathbf{(K1)}\quad
\exists A>0,\ \exists m\in\mathbb N,\ \forall n,\forall x,\forall y,\qquad
|\eta_{n,x}(y)|\le A(1+|y|)^{-m}.
\]

\[
\mathbf{(K2)}\quad
\exists A>0,\ \forall n,\forall y,\qquad
\sum_{x\in\Lambda_n} a_n^4 |\eta_{n,x}(y)|\le A.
\]

## Consequence

\[
\mathbf{(K1)}+\mathbf{(K2)}
\Longrightarrow
\sum_{x\in\Lambda_n}|(W_n f)(x)|^2\le C\|f\|_{\mathcal S,m}^2.
\]

Hence

\[
\mathbf{(K1)}+\mathbf{(K2)}
\Longrightarrow
\mathbf{(L2b)}
\Longrightarrow
\mathbf{(L2)}
\quad\text{once }\mathbf{(L2a)}\text{ and locality of }\Gamma_n\text{ are in place.}
\]

## Next admissible micro-fix

\[
\boxed{\text{specialize } \eta_{n,x}\text{ for the actual }W_n\text{ used in the repository}}
\]
