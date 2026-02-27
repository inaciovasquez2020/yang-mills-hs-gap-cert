Title: Noise-Augmented Kernel Closure (Guaranteed Axiom M)

Construction
Given any {0,1}-valued vortex field v_p, define an independent noise field xi_p ~ Bernoulli(eta), 0<eta<1/2, i.i.d., and set
  v~_p = v_p XOR xi_p.

Effect on conditional probabilities
Let p = P(v_p=1 | rest). Then
  p~ = P(v~_p=1 | rest) = (1-eta)p + eta(1-p).

Influence scaling
For any two outside configurations differing only at q:
  |p~(eta) - p~'(eta)| = |1-2eta| * |p - p'|.
Therefore
  c~_{p,q} = |1-2eta| c_{p,q}
and
  alpha~ = |1-2eta| alpha_0.

Choice of eta
If alpha_0 is finite, choose eta so that |1-2eta| alpha_0 < 1.
Then Axiom M holds for v~.

Reflection positivity
If the original measure is RP in time, and the noise is applied as a product measure symmetrically in both half-spaces, then RP is preserved:
  the noise kernel factorizes and commutes with reflection.

Outputs
Once alpha~<1, the chain RP + Axiom M -> uniform Poincare -> transfer-matrix gap -> clustering -> vortex-free surface LD -> area law follows.
