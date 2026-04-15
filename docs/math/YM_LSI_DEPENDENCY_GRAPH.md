# Dependency Graph for the Canonical Missing Input

## Status

Conditional.

## Root target

\[
\exists B>0,\ \exists m\in\mathbb N,\ \forall t\in\mathbb R,\ \forall n,\ \forall f\in\mathcal S(\mathbb R^4,\mathfrak g),\qquad
\int e^{\,t\,\phi(f)}\,d\mu_{\Lambda_n,a_n}
\le
\exp\!\bigl(B\,t^2\|f\|_{\mathcal S,m}^2\bigr).
\]

## Immediate reduction

\[
\mathbf{(L1)}+\mathbf{(L2)}+\mathbf{(L3)}
\Longrightarrow
\text{root target.}
\]

## Node \(\mathbf{(L1)}\)

\[
\mathbf{(L1)}\quad
\exists \rho>0,\ \forall n,\ \mu_{\Lambda_n,a_n}\text{ satisfies }LSI(\rho).
\]

Weakest sufficient subroutes:

\[
\mathbf{(L1a)}\quad
\exists \rho>0,\ \forall n,\ \forall H,\qquad
\Gamma_{2,n}(H)\ge \rho\,\Gamma_n(H).
\]

or

\[
\mathbf{(L1b)}\quad
\text{uniform finite-volume Brascamp--Lieb inequality}
\]
together with
\[
\mathbf{(L1c)}\quad
\text{uniform strict convexity lower bound for the effective lattice action.}
\]

## Node \(\mathbf{(L2)}\)

\[
\mathbf{(L2)}\quad
\exists C>0,\ \exists m\in\mathbb N,\ \forall n,\ \forall f,\qquad
\Gamma_n(\phi(f))\le C\|f\|_{\mathcal S,m}^2.
\]

Weakest sufficient subroute:

\[
\mathbf{(L2a)}\quad
\phi(f)=\sum_{x\in\Lambda_n}\langle K_{n,f}(x),U_x\rangle
\]

and

\[
\mathbf{(L2b)}\quad
\sum_{x\in\Lambda_n}|K_{n,f}(x)|^2\le C\|f\|_{\mathcal S,m}^2,
\]

plus locality of \(\Gamma_n\), yielding

\[
\Gamma_n(\phi(f))
\lesssim
\sum_{x\in\Lambda_n}|K_{n,f}(x)|^2.
\]

## Node \(\mathbf{(L3)}\)

\[
\mathbf{(L3)}\quad
\forall n,\ \forall f,\qquad
\int \phi(f)\,d\mu_{\Lambda_n,a_n}=0.
\]

Weakest sufficient subroute:

\[
\mathbf{(L3a)}\quad
\mu_{\Lambda_n,a_n}\text{ is invariant under }\phi\mapsto -\phi
\]

or any symmetry implying odd one-point functions vanish.

## Current frontier

\[
\boxed{\mathbf{(L1)}+\mathbf{(L2)}+\mathbf{(L3)}}
\]

## Next admissible micro-fix

\[
\boxed{\mathbf{(L3)}\to \mathbf{(L3a)}}
\]
