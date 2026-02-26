import ALSTAR.Axioms.QuotientGI

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (Q : H →ₗ[ℝ] H)

/-
Next proof targets (no axioms):

(1) CoerciveGIQ (Q:=Q) → CoerciveGIQ_proj (Q:=Q).
(2) Under symmetry/self-adjointness hypotheses on Q, prove converse.
(3) Replace Q by the actual gauge-invariant YM operator after OS reconstruction,
    and identify ZeroModes with gauge/collective-coordinate modes.
-/

end

end ALSTAR
