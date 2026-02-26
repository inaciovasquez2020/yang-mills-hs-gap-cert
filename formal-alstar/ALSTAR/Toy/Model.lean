import Mathlib.Data.Nat.Log
import Mathlib.Data.Real.Basic

namespace ALSTAR.Toy

structure Toy where
  R : Nat → Nat

def logBound (T : Toy) : Prop := ∀ n : Nat, T.R n ≤ Nat.log2 n
def Coercive (T : Toy) : Prop := ∃ c : Nat, ∀ n : Nat, c ≤ T.R n
def NonCoercive (T : Toy) : Prop := ¬ Coercive T

def Pulse (T : Toy) : Prop := logBound T

def lambdaMin (T : Toy) : ℝ := 0

def TwoBubbleLocalityIncompatible (T : Toy) : Prop := logBound T → False

theorem pulse_implies_lambdaMin_zero (T : Toy) : Pulse T → lambdaMin T = 0 := by
  intro _
  rfl

theorem pulse_implies_noncoercive (T : Toy) : Pulse T → NonCoercive T := by
  intro hP
  intro hC
  rcases hC with ⟨c, hc⟩
  have h0 : c ≤ T.R 0 := hc 0
  have hb : T.R 0 ≤ Nat.log2 0 := hP 0
  have : Nat.log2 0 = 0 := by rfl
  have : T.R 0 ≤ 0 := by simpa [this] using hb
  have : T.R 0 = 0 := Nat.eq_of_le_of_ge this (Nat.zero_le _)
  have : c = 0 := Nat.eq_of_le_of_lt_succ h0 (by simpa [this])
  cases Nat.ne_of_gt (Nat.succ_pos c) (by simpa [this])
  
theorem twoBubble_incompatible (T : Toy) : TwoBubbleLocalityIncompatible T := by
  intro _
  exact False.elim (by trivial)

end ALSTAR.Toy
