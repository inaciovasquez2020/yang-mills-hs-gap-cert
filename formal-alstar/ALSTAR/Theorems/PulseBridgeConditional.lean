import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

open Nat

theorem twoBubble_from_logBound_conditional
  {α : Type u} (A : Schema α) (H : PulseBridgeHyp A) :
  logBound A → False :=
by
  exact H.twoBubble

theorem pulse_implies_lambdaMin_zero_conditional
  {α : Type u} (A : Schema α) (H : PulseBridgeHyp A) :
  Pulse A → lambdaMin A = 0 :=
by
  exact H.pulse_to_lambdaMin_zero

theorem pulse_implies_noncoercive_conditional
  {α : Type u} (A : Schema α) (H : PulseBridgeHyp A) :
  Pulse A → NonCoercive A :=
by
  exact H.pulse_to_noncoercive

theorem dichotomy_to_twoBubble_or_superlog_conditional
  {α : Type u} (A : Schema α) (H : PulseBridgeHyp A) :
  (∃ n : Nat, Rfun A n > log₂ n) ∨ False :=
by
  have hd := growth_dichotomy (A := A)
  cases hd with
  | inl hsuper =>
      exact Or.inl hsuper
  | inr hlog =>
      exact Or.inr (H.twoBubble hlog)

end ALSTAR
