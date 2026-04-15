# L2b from a Sampling/Averaging Operator Bound

## Status

Conditional.

## Target

\[
\sum_{x\in\Lambda_n}|(W_n f)(x)|^2\le C\|f\|_{\mathcal S,m}^2.
\]

## Weakest sufficient micro-fix

Assume
\[
(W_n f)(x)=a_n^{4/2}\int_{\mathbb R^4}\eta_{n,x}(y)f(y)\,dy,
\]
where the kernels \(\eta_{n,x}\) satisfy a uniform Schwartz-kernel bound: there exist \(A>0\) and \(m\in\mathbb N\) such that
\[
\sup_{n,x,y}\,
(1+|y|)^m\,|\eta_{n,x}(y)|
\le A,
\]
and a uniform overlap bound
\[
\sup_n\sup_{y\in\mathbb R^4}
\sum_{x\in\Lambda_n} a_n^4 |\eta_{n,x}(y)|
\le A.
\]

Then
\[
|(W_n f)(x)|
\le
a_n^{4/2}\int |\eta_{n,x}(y)|\,|f(y)|\,dy
\le
A\,a_n^{4/2}\,\|f\|_{\mathcal S,m}\int (1+|y|)^{-m}dy.
\]

Using Cauchy--Schwarz/Schur summation with the overlap bound,
\[
\sum_{x\in\Lambda_n}|(W_n f)(x)|^2
\le
C\|f\|_{\mathcal S,m}^2
\]
for a constant \(C\) independent of \(n\).

## Reduction lock

\[
\text{uniform kernel decay}+\text{uniform overlap bound}
\Longrightarrow
\mathbf{(L2b)}.
\]

## Next admissible micro-fix

\[
\boxed{\text{isolate the exact kernel/overlap assumptions satisfied by the chosen }W_n}
\]
