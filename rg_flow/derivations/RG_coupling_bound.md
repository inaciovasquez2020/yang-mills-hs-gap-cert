RG flow inequality for coupling boundedness

Goal
Derive an inequality ensuring the running coupling g(Λ) remains bounded along RG flow.

1. One-step RG recursion

Let Λ_{n+1} = Λ_n / b with b > 1.

Write flow:

g_{n+1} = g_n + β(g_n) log b + R_n

where:
β(g) is the beta function,
R_n are higher-order corrections controlled by irrelevant operators.

2. Asymptotic freedom structure

For SU(N):

β(g) = -β0 g^3 - β1 g^5 + O(g^7)
β0 > 0.

Thus for small g:

g_{n+1} ≤ g_n - β0 g_n^3 log b + C g_n^5

3. Differential inequality approximation

Treat continuous scale μ:

μ dg/dμ = β(g)

For small g:

dg/dt ≤ -β0 g^3 + C g^5
where t = log μ.

4. Uniform bound condition

Define H(g) = 1/g^2.

Then:

dH/dt ≥ 2β0 - C g^2

Thus for sufficiently small initial g:

H(t) ≥ H(0) + β0 t

Therefore:

g(t)^2 ≤ 1 / (H(0) + β0 t)

5. Infrared direction

As μ decreases (t negative), coupling grows.

Boundedness condition:

Require existence of t_* such that:

g(t)^2 ≤ G_max^2 < ∞ for all scales considered.

This holds if:

Initial data lies in perturbative basin and RG flow does not cross Landau-type singularity.

6. Discrete RG inequality

Assume existence of constants c1, c2:

g_{n+1}^2 ≤ g_n^2 / (1 + 2β0 g_n^2 log b) + c2 g_n^6

Inductively:

g_n^2 ≤ 1 / (1/g_0^2 + 2β0 n log b)

Thus g_n bounded uniformly for finite RG depth.

7. Required hypothesis for Mourre

There exists G_max such that:

sup_n g_n ≤ G_max < ∞

This ensures:

Relative bound constant a < 1 in V relative to H_0 independent of cutoff.

8. Remaining obstruction

Need nonperturbative control beyond perturbative β-function regime.

Specifically:

Prove RG map satisfies monotonic inequality:

g_{n+1}^2 ≤ g_n^2 (1 - c g_n^2)

for some c > 0 at small g.

Conclusion

If asymptotic freedom plus RG monotonicity inequality hold nonperturbatively,
then coupling remains bounded along flow,
which ensures interaction relative boundedness,
which enables uniform Mourre estimate.
