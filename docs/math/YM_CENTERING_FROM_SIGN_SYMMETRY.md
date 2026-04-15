# Centering from Sign Symmetry

## Status

Conditional.

## Target

\[
\forall n,\ \forall f\in\mathcal S(\mathbb R^4,\mathfrak g),\qquad
\int \phi(f)\,d\mu_{\Lambda_n,a_n}=0.
\]

## Weakest sufficient lemma

Assume for every \(n\) the measure \(\mu_{\Lambda_n,a_n}\) is invariant under the sign involution
\[
\phi \mapsto -\phi.
\]

Then for every odd measurable observable \(H\),
\[
\int H(\phi)\,d\mu_{\Lambda_n,a_n}
=
\int H(-\phi)\,d\mu_{\Lambda_n,a_n}
=
-\int H(\phi)\,d\mu_{\Lambda_n,a_n},
\]
hence
\[
\int H(\phi)\,d\mu_{\Lambda_n,a_n}=0.
\]

Applying this to
\[
H(\phi):=\phi(f),
\]
which is odd in \(\phi\), yields
\[
\int \phi(f)\,d\mu_{\Lambda_n,a_n}=0.
\]

## Reduction lock

\[
\text{sign symmetry of }\mu_{\Lambda_n,a_n}
\Longrightarrow
\mathbf{(L3)}.
\]
