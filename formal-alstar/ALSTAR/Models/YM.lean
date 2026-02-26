import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.QuotientGI

namespace ALSTAR

/-- Concrete (placeholder) model tying Schema to a YM growth functional Rym. -/
structure YMParams where
  Rym : ℕ → ℕ

def YM.Schema (p : YMParams) : Schema Unit :=
  { R := p.Rym }

/-- YM operator package (placeholder for the gauge-invariant Hamiltonian/Jacobi map). -/
structure YMOperator where
  H : Type
  [Hn : NormedAddCommGroup H]
  [Hi : InnerProductSpace ℝ H]
  Q : H →ₗ[ℝ] H

attribute [instance] YMOperator.Hn YMOperator.Hi

/--
Gauge-invariant coercivity statement, *after quotienting zero modes*:
coercivity of Q on (ker Q)ᗮ.
-/
def YM.CoerciveGI (op : YMOperator) : Prop :=
  CoerciveGIQ (Q := op.Q)

end ALSTAR
