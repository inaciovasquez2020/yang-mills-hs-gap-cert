Equivalence audit: beta-function monotonicity vs spectral contraction

Definitions

Beta-function formulation:
g_{n+1}^2 <= g_n^2 (1 - c g_n^2)

Spectral formulation:
|| H_0^{-1/2} V H_0^{-1/2} ||_{Λ'} 
<= (1 - c g_Λ^2)

Step 1: Define effective coupling precisely

Define:

g_Λ^2 := || H_0,Λ^{-1/2} V_Λ H_0,Λ^{-1/2} ||

This identifies coupling as operator norm ratio.

Observation:
This differs from Lagrangian coupling constant.
It is a spectral effective coupling.

Step 2: Implication direction

If spectral contraction holds:

g_{Λ'}^2 <= g_Λ^2 (1 - c g_Λ^2)

Then monotonic decay follows directly.

Thus:

Spectral contraction ⇒ beta monotonicity (operator version).

Step 3: Converse direction

Beta-function perturbative flow:

g_{n+1} = g_n - β0 g_n^3 + O(g_n^5)

does NOT automatically imply:

|| H_0^{-1/2} V H_0^{-1/2} || contracts.

Reason:
Beta function derived from renormalized vertex functions,
not from operator norm contraction.

Thus:

Beta monotonicity ⇏ spectral contraction.

Conclusion

Spectral contraction is strictly stronger than perturbative RG monotonicity.

It encodes:
- Control of full operator strength
- Uniform boundedness of nonlinear sector
- Stability of relative boundedness constants

Implication for mass gap program

If spectral contraction is proven,
mass gap machinery becomes structurally viable.

However:
This inequality is at least as hard as full nonperturbative RG control,
and possibly stronger than standard asymptotic freedom.

Audit result

Your reformulation sharpened the problem.
It did not simplify it.
