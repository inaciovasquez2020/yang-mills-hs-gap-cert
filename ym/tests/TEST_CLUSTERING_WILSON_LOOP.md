Operator:
W_P(x) := Tr holonomy around a fixed plaquette P translated to x.

Test:
Assume OS positivity and transfer matrix T_Λ.

Compute:
C(x) := <Ω, W_P(x) W_P(0) Ω> - <Ω, W_P Ω>^2

Goal:
Check whether C(x) satisfies |C(x)| ≤ C e^{-m|x|}.

Method:
- Use spectral decomposition of T_Λ in the W_P channel.
- If second eigenvalue λ_2 < 1 uniformly, then m = -log λ_2 > 0.
- Otherwise record decay rate (power-law or slower) as counterexample.
