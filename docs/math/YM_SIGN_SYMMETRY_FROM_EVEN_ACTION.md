# Sign Symmetry from Even Finite-Volume Action

## Status

Conditional.

## Weakest sufficient lemma

Assume for every \(n\) the finite-volume measure admits a density
\[
d\mu_{\Lambda_n,a_n}(\phi)=Z_n^{-1}e^{-S_n(\phi)}\,d\nu_n(\phi),
\]
where \(d\nu_n\) is a reference measure and \(S_n\) is the effective lattice action.

Assume moreover
\[
S_n(-\phi)=S_n(\phi)
\qquad\text{and}\qquad
d\nu_n(-\phi)=d\nu_n(\phi)
\]
for every field configuration \(\phi\).

Then for every bounded measurable observable \(F\),
\[
\int F(-\phi)\,d\mu_{\Lambda_n,a_n}(\phi)
=
Z_n^{-1}\int F(-\phi)e^{-S_n(\phi)}\,d\nu_n(\phi).
\]

Applying the change of variables \(\psi=-\phi\), and using the two symmetry assumptions,
\[
\int F(-\phi)\,d\mu_{\Lambda_n,a_n}(\phi)
=
Z_n^{-1}\int F(\psi)e^{-S_n(\psi)}\,d\nu_n(\psi)
=
\int F(\psi)\,d\mu_{\Lambda_n,a_n}(\psi).
\]

Therefore
\[
\int F(-\phi)\,d\mu_{\Lambda_n,a_n}
=
\int F(\phi)\,d\mu_{\Lambda_n,a_n},
\]
so
\[
(\phi_\#\mu_{\Lambda_n,a_n})=((-\phi)_\#\mu_{\Lambda_n,a_n}).
\]

## Reduction lock

\[
\text{even action}+\text{even reference measure}
\Longrightarrow
\text{sign symmetry}
\Longrightarrow
\text{centering}
\Longrightarrow
\mathbf{(L3)}.
\]
