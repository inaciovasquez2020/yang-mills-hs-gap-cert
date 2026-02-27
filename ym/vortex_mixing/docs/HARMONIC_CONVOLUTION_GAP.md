# Deterministic Contraction via SU(2) Convolution Gap

This file records the exact analytic condition needed to prove Dobrushin contraction (Axiom M) without noise: a uniform spectral gap for the induced SU(2) convolution operator on blocked plaquette distributions.

* For a block of size M, define $\mu_{M,U}$ as the distribution of blocked SU(2) plaquette under Haar–gauge averaging.
* Uniform total–variation decay as $M\to\infty$ implies a contraction bound \(c_{p,q}\le C\rho^M\) with \(\rho<1\).

The missing analytic theorem is:
> There exist constants \(C,\rho<1\) such that for all M and all fine backgrounds U:
>   \|\mu_{M,U} - \mathrm{Haar}\|_{\mathrm{TV}}\le C\rho^M.

Once this is proven, the Dobrushin sum $\alpha\le N(M)\cdot C\rho^M<1$ for large M.

