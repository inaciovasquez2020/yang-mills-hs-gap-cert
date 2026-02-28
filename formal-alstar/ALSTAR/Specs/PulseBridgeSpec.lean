import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic
import ALSTAR.Axioms.Basic
import ALSTAR.Axioms.Coercivity

namespace ALSTAR

open Nat

def Rfun {α : Type u} (A : Schema α) : Nat → Nat :=
  A.R

def logBound {α : Type u} (A : Schema α) : Prop :=
  ∀ n : Nat, Rfun A n ≤ log₂ n

def NonCoercive {α : Type u} (A : Schema α) : Prop :=
  ¬ Coercive A

def Pulse {α : Type u} (A : Schema α) : Prop :=
  logBound A

def lambdaMin {α : Type u} (A : Schema α) : ℝ :=
  0

def TwoBubbleLocalityIncompatible {α : Type u} (A : Schema α) : Prop :=
  logBound A → False

structure PulseBridgeHyp {α : Type u} (A : Schema α) : Prop where
  twoBubble :
    TwoBubbleLocalityIncompatible Apulse_to_noncoercive :
    Pulse A → NonCoercive A

theorem growth_dichotomy
  {α : Type u}
  (A : Schema α) :
  (∃ n : Nat, Rfun A n > log₂ n) ∨ logBound A :=
by
  by_cases h : ∃ n, Rfun A n > log₂ n
  · exact Or.inl h
  · refine Or.inr ?_
    intro n
    have : ¬ Rfun A n > log₂ n := by
      intro hgt
      exact h ⟨n, hgt⟩
    exact le_of_not_gt this

end ALSTAR
