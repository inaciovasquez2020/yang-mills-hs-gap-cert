# WTR Contractive Gap

## Conditional closure lemma

Assume there exist:
- a rigorously specified admissible class \mathcal A,
- constants c_main>0, c_gain\ge 0, \eta>0,
- quadratic forms E_main, E_gain on \mathcal A,

such that for all u \in \mathcal A \setminus \{0\}:

\[
E_{\mathrm{main}}(u)\ge c_{\mathrm{main}}\|u\|_{L^2}^2,
\qquad
E_{\mathrm{gain}}(u)\le c_{\mathrm{gain}}\|u\|_{L^2}^2,
\qquad
c_{\mathrm{gain}}<(1-\eta)c_{\mathrm{main}}.
\]

Then

\[
E_{\mathrm{gain}}(u)\le (1-\eta)E_{\mathrm{main}}(u)
\qquad
(\forall u\in\mathcal A\setminus\{0\}),
\]

hence RPD_ERROR_GAIN_LEMMA holds conditionally, and RPD_6_TWO_BUBBLE_INCOMPATIBILITY is unblocked conditionally.

## Fixed operator decomposition

\[
X:=H^1_{\mathrm{loc}}(\mathbb R^4;V)\cap L^2(\mathbb R^4;V),
\qquad
Y:=L^2(\mathbb R^4;V),
\]

\[
\mathcal A:=\Bigl\{u\in X:\ \Pi_{\ker L}u=0,\ \Gamma u=0,\ E_{\mathrm{main}}(u)<\infty,\ E_{\mathrm{gain}}(u)<\infty\Bigr\},
\]

\[
Q(u):=\langle Lu,u\rangle_{L^2},
\qquad
E_{\mathrm{main}}(u):=\langle L_{\mathrm{coer}}u,u\rangle_{L^2},
\qquad
E_{\mathrm{gain}}(u):=\bigl|\langle L_{\mathrm{err}}u,u\rangle_{L^2}\bigr|,
\]

with

\[
L=L_{\mathrm{coer}}+L_{\mathrm{err}}
\quad\text{on }\mathcal A.
\]

## Minimal remaining open lemma

Prove, on the actual Yang--Mills operator/data path,

\[
\exists \eta>0\ \forall u\in\mathcal A\setminus\{0\}:\qquad
E_{\mathrm{gain}}(u)\le (1-\eta)\,E_{\mathrm{main}}(u).
\]
