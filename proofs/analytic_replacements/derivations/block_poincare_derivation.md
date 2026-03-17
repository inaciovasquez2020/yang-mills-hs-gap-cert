# Block Poincaré Derivation

Let \(B_L\subset\mathbb{Z}^d\) be a lattice cube.

Using the spectral-gap identity

\[
\lambda_1(B_L)
=
\inf_{f \perp 1}
\frac{\sum_{\langle x,y\rangle}(f(x)-f(y))^2}
{\sum_x f(x)^2},
\]

and

\[
\lambda_1(B_L) \ge c L^{-2},
\]

we obtain

\[
\sum_x (f(x)-\bar f)^2
\le
C L^2
\sum_{\langle x,y\rangle}(f(x)-f(y))^2.
\]

Therefore

\[
\|Q_L f\|^2 \le C L^2 \langle f,(-\Delta)f\rangle.
\]
