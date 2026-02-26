import ALSTAR.Models.YM
import ALSTAR.Axioms.Pulse

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/--
Attach a pulse interpretation to the YM schema:
the schema growth function bounds the iterated commutator norms.
-/
def YM.PulseModel (p : YMParams) (H0 : (H →L[ℝ] H)) (Good : (H →L[ℝ] H) → Prop) : Prop :=
  PulseBound (H := H) (A := YM.Schema p) H0 Good

end

end ALSTAR
