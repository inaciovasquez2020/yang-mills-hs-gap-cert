# Plaquette Spectrum Derivation

Consider the discrete plaquette Laplacian on the \(n\)-cycle:

\[
(Lf)(j)=2f(j)-f(j-1)-f(j+1).
\]

The Fourier modes

\[
\phi_k(j)=e^{2\pi i k j/n}
\]

are eigenfunctions with eigenvalues

\[
\lambda_k
=
2-2\cos\left(\frac{2\pi k}{n}\right),
\qquad
k=0,\dots,n-1.
\]

Hence the spectral gap is

\[
\lambda_1
=
2-2\cos\left(\frac{2\pi}{n}\right).
\]

Using

\[
1-\cos x \ge \frac{x^2}{4},
\]

we obtain

\[
\lambda_1 \ge \frac{4\pi^2}{n^2}.
\]

Therefore

\[
n^2\lambda_1 \ge 4\pi^2.
\]
