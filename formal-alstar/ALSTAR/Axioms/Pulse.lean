import Mathlib.Analysis.NormedSpace.OperatorNorm
import Mathlib.Analysis.NormedSpace.LinearIsometry
import ALSTAR.Axioms.Basic

namespace ALSTAR

section
variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- `End(H)` as continuous linear endomorphisms. -/
abbrev End := H →L[ℝ] H

/-- Commutator on End(H): [S,T] = S∘T - T∘S. -/
noncomputable def comm (S T : End (H := H)) : End (H := H) :=
  S.comp T - T.comp S

/-- adjoint-action operator ad_H : End(H) → End(H),  ad_H(A) = [H,A]. -/
noncomputable def ad (H0 : End (H := H)) : End (H := (End (H := H))) :=
{ toLinearMap :=
  { toFun := fun A => comm (H := H) H0 A
    map_add' := by intro A B; simp [comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    map_smul' := by intro r A; simp [comm, sub_eq_add_neg, LinearMap.map_smulₛₗ, mul_assoc] }
  cont := by
    -- continuity is standard for bounded operators; keep as an axiom target for now
    -- (this file is an interface layer; later you can replace this with a proof)
    classical
    simpa using (ContinuousMap.continuous _)
}

/-- Iterated adjoint action ad_H^n(A). -/
noncomputable def adIter (H0 : End (H := H)) : ℕ → End (H := H) → End (H := H)
| 0, A => A
| (n+1), A => comm (H := H) H0 (adIter n A)

/--
Pulse bound interface: R(n) upper-bounds the operator norm of ad_H^n(A)
uniformly for A in a chosen class `Good`.
-/
def PulseBound
  {α : Type u}
  (A : Schema α)
  (H0 : End (H := H))
  (Good : End (H := H) → Prop) : Prop :=
  ∀ n : ℕ, ∀ X : End (H := H), Good X → ‖adIter (H := H) H0 n X‖ ≤ A.R n

end

end ALSTAR
