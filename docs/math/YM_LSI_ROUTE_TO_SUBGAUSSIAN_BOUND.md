# Uniform LSI/Herbst Route to the Subgaussian Bound

\[
\textbf{Canonical target}
\]

\[
\exists B>0,\ \exists m\in\mathbb N,\ \forall t\in\mathbb R,\ \forall n,\ \forall f\in\mathcal S(\mathbb R^4,\mathfrak g),\qquad
\int e^{\,t\,\phi(f)}\,d\mu_{\Lambda_n,a_n}
\le
\exp\!\bigl(B\,t^2\|f\|_{\mathcal S,m}^2\bigr).
\]

\[
\textbf{Step 1. Uniform centeredness.}
\]

\[
\forall n,\ \forall f\in\mathcal S(\mathbb R^4,\mathfrak g),\qquad
\int \phi(f)\,d\mu_{\Lambda_n,a_n}=0.
\]

\[
\textbf{Step 2. Uniform entropy inequality on the lattice family.}
\]

\[
\exists \rho>0,\ \forall n,\ \forall G>0,\qquad
\operatorname{Ent}_{\mu_{\Lambda_n,a_n}}(G)
\le
\frac1{2\rho}\int \frac{\Gamma_n(G)}{G}\,d\mu_{\Lambda_n,a_n}.
\]

Here
\[
\operatorname{Ent}_{\mu}(G):=\int G\log G\,d\mu-\Bigl(\int G\,d\mu\Bigr)\log\Bigl(\int G\,d\mu\Bigr),
\]
and \(\Gamma_n\) is the lattice carré-du-champ.

\[
\textbf{Step 3. Uniform gradient bound for the smeared field.}
\]

\[
\exists C>0,\ \exists m\in\mathbb N,\ \forall n,\ \forall f\in\mathcal S(\mathbb R^4,\mathfrak g),\qquad
\Gamma_n(\phi(f))
\le
C\,\|f\|_{\mathcal S,m}^2
\quad
\mu_{\Lambda_n,a_n}\text{-a.s.}
\]

\[
\textbf{Step 4. Apply Step 2 to }G=e^{\lambda\phi(f)}.
\]

Then
\[
\Gamma_n(G)=\lambda^2\,\Gamma_n(\phi(f))\,e^{\lambda\phi(f)},
\]
hence by Step 3,
\[
\operatorname{Ent}_{\mu_{\Lambda_n,a_n}}\!\bigl(e^{\lambda\phi(f)}\bigr)
\le
\frac{\lambda^2 C}{2\rho}\,\|f\|_{\mathcal S,m}^2
\int e^{\lambda\phi(f)}\,d\mu_{\Lambda_n,a_n}.
\]

\[
\textbf{Step 5. Differential inequality for the log-Laplace transform.}
\]

Define
\[
\Psi_{n,f}(\lambda):=
\log\int e^{\lambda\phi(f)}\,d\mu_{\Lambda_n,a_n}.
\]

Then
\[
\lambda\Psi'_{n,f}(\lambda)-\Psi_{n,f}(\lambda)
\le
\frac{\lambda^2 C}{2\rho}\,\|f\|_{\mathcal S,m}^2.
\]

\[
\textbf{Step 6. Integrate the Herbst inequality.}
\]

Using
\[
\Psi_{n,f}(0)=0,\qquad \Psi'_{n,f}(0)=\int \phi(f)\,d\mu_{\Lambda_n,a_n}=0,
\]
one obtains
\[
\Psi_{n,f}(\lambda)
\le
\frac{C}{2\rho}\,\lambda^2\|f\|_{\mathcal S,m}^2.
\]

\[
\textbf{Step 7. Exponentiate.}
\]

\[
\int e^{\,\lambda\,\phi(f)}\,d\mu_{\Lambda_n,a_n}
\le
\exp\!\Bigl(\frac{C}{2\rho}\lambda^2\|f\|_{\mathcal S,m}^2\Bigr).
\]

Therefore the canonical target holds with
\[
B=\frac{C}{2\rho}.
\]
