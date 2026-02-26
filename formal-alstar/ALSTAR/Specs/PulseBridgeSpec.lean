import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import ALSTAR.Axioms.Basic

namespace ALSTAR

open Nat

def Rfun (A : Schema α) : Nat → Nat := A.R

def logBound (A : Schema α) : Prop :=
  ∀ n : Nat, Rfun A n ≤ log₂ n

def Coercive (A : Schema α) : Prop :=
  ∃ c : Nat, ∀ n : Nat, c ≤ Rfun A n

def NonCoercive (A : Schema α) : Prop :=
  ¬ Coercive A

def TwoBubbleLocalityIncompatible (A : Schema α) : Prop :=
  logBound A → False

def Pulse (A : Schema α) : Prop :=
  logBound A

def lambdaMin (A : Schema α) : ℝ :=
  0

structure PulseBridgeHyp {α : Type u} (A : Schema α) : Prop where
  twoBubble : TwoBubbleLocalityIncompatible A
  pulse_to_lambdaMin_zero : Pulse A → lambdaMin A = 0
  pulse_to_noncoercive : Pulse A → NonCoercive A

theorem growth_dichotomy {α : Type u} (A : Schema α) :
  (∃ n : Nat, Rfun A n > log₂ n) ∨ logBound A :=
by
  by_cases h : ∃ n, Rfun A n > log₂ n
  · exact Or.inl h
  · refine Or.inr ?_
    intro n
    have hn : ¬ Rfun A n > log₂ n := by
      intro hgt
      exact h ⟨n, hgt⟩
    exact le_of_not_gt hn

end ALSTAR
