Goal: prove exponential clustering for one explicit gauge-invariant local operator.

Pick operator:
O(x) := Tr(F_{μν}F^{μν})(x)  (or a small Wilson loop W_γ(x) on a fixed plaquette)

Target:
| <Ω, O(x) O(0) Ω> - <Ω,OΩ>^2 | ≤ C e^{-m|x|}.

Route A (transfer matrix + spectral representation):
1. Work in finite volume with OS positivity and transfer matrix T_Λ.
2. Identify H_Λ = -(1/a) log T_Λ and O as an OS-compatible observable.
3. Show a uniform spectral gap m_Λ>0 in the O-channel implies clustering with rate m_Λ.
4. Upgrade to uniform m_Λ ≥ m_* via RG stability or an independent IR bound.

Route B (random current / reflection positivity inequalities):
1. Use reflection positivity to get a correlation inequality for O.
2. Combine with infrared bound or chessboard estimate to obtain exponential decay.

Counterexample route:
Find a sequence of admissible states in the O-channel forcing power-law decay (gapless).
