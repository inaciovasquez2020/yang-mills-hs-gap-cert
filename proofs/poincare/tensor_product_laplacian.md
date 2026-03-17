# Tensor Product Laplacian Decomposition

Let \(B_L^{(d)} = [1,L]^d\).

The Laplacian decomposes as

\[
L_{B_L^{(d)}} =
\sum_{i=1}^{d}
I^{\otimes (i-1)} \otimes L_{P_L} \otimes I^{\otimes (d-i)}.
\]

Therefore eigenfunctions factorize

\[
\phi_{k_1,\dots,k_d}(x_1,\dots,x_d)
=
\prod_{i=1}^{d}
\sin\left(\frac{\pi k_i x_i}{L+1}\right).
\]

Eigenvalues:

\[
\lambda(k_1,\dots,k_d)
=
\sum_{i=1}^{d}
\lambda_{P_L}(k_i).
\]
