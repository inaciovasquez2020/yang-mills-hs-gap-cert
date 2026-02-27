# Noise–Augmented Kernel to Enforce Contraction

Given any blocked vortex indicator $v_p$, define a noise flip with probability $\eta\in(0,1/2)$:
\[
\tilde v_p = v_p\oplus\xi_p,
\quad \xi_p\sim\mathrm{Bernoulli}(\eta).
\]

Then conditional probabilities transform as:
\[
\tilde p=(1-\eta)p+\eta(1-p),
\]
and influences scale by \(|1-2\eta|\). Choosing \(\eta\) so that \(|1-2\eta|\cdot\alpha_0<1\) enforces Axiom M.

This preserves reflection positivity when applied symmetrically.

