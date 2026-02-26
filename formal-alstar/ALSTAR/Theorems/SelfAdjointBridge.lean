import ALSTAR.Axioms.SelfAdjoint

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/-
Next proof targets (no axioms here):

(1) If `SelfAdjointQ Q` and `GapOnPhys Q`, then `CoerciveGIQ (Q:=Q)`.
    (This is essentially definitional, but keep it explicit as a named bridge.)

(2) If `SelfAdjointQ Q` and `PositiveOnPhys Q`, then Rayleigh quotient is ≥ 0.

(3) Under compactness/discrete spectrum hypotheses, show:
      GapOnPhys ↔ inf_{x ⟂ ker Q} Rayleigh(x) > 0.
-/

theorem gapOnPhys_implies_coerciveGIQ :
  GapOnPhys (Q := Q) → CoerciveGIQ (Q := Q) :=
by
  intro h
  exact h

end

end ALSTAR
