Minimal RG conditions sufficient for Mourre stability

Goal
Replace strong spectral contraction by weaker, windowed conditions sufficient to carry the Mourre estimate through RG.

Notation
H_Λ = H_0,Λ + V_Λ
L_Λ = H_0,Λ
A is momentum-space dilation generator

Target Mourre estimate on window I ⊂ (0, ∞):
1_I(H_Λ) i[H_Λ, A] 1_I(H_Λ) >= c_I 1_I(H_Λ)

Minimal sufficient conditions

C1 Form boundedness (uniform)
There exist a < 1 and b < ∞ independent of Λ such that:
|<ψ, V_Λ ψ>| <= a <ψ, H_0,Λ ψ> + b ||ψ||^2

C2 Commutator form boundedness (uniform)
There exist a_A < 1 and b_A < ∞ independent of Λ such that:
|<ψ, i[V_Λ, A] ψ>| <= a_A <ψ, H_0,Λ ψ> + b_A ||ψ||^2

C3 C^1(A) regularity on a common core
H_Λ is of class C^1(A) with commutator defined as a closed form on the core.

C4 Quadratic positive commutator for H_0
i[H_0,Λ, A] >= 2 H_0,Λ - Err_Λ
with Err_Λ form-bounded by epsilon H_0,Λ + C epsilon^{-1} and epsilon uniform.

Derivation of Mourre estimate

i[H_Λ, A] = i[H_0,Λ, A] + i[V_Λ, A]
>= 2H_0,Λ - Err_Λ - a_A H_0,Λ - b_A

Choose epsilon and require (2 - epsilon - a_A) > 0.

Then on the spectral window I, use:
H_0,Λ <= H_Λ + const
to obtain:
1_I(H_Λ) i[H_Λ, A] 1_I(H_Λ) >= c_I 1_I(H_Λ)

Conclusion

Mourre stability does not require RG contraction of ||H_0^{-1/2} V H_0^{-1/2}||.
It requires uniform form bounds for V and its commutator with A, plus C^1(A) regularity.

Remaining obstruction

Prove uniform bounds C1 and C2 nonperturbatively for 4D Yang–Mills.
