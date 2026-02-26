import ALSTAR.Specs.PulseBridgeSpec
import ALSTAR.Toy.Model

namespace ALSTAR

open Nat

def ToySchema : Type := Unit

def toySchemaToSchema (T : ALSTAR.Toy.Toy) : Schema ToySchema :=
{ R := T.R }

theorem toy_discharge_PulseBridgeHyp (T : ALSTAR.Toy.Toy) :
  PulseBridgeHyp (toySchemaToSchema T) :=
by
  refine ⟨?_, ?_, ?_⟩
  · intro hlog
    exact False.elim (by trivial)
  · intro _
    rfl
  · intro hP
    intro hC
    rcases hC with ⟨c, hc⟩
    have h0 : c ≤ (toySchemaToSchema T).R 0 := hc 0
    have hb : (toySchemaToSchema T).R 0 ≤ log₂ 0 := by
      have : ∀ n, (toySchemaToSchema T).R n ≤ log₂ n := by
        intro n
        exact hP n
      exact this 0
    have : log₂ 0 = 0 := by rfl
    have : (toySchemaToSchema T).R 0 ≤ 0 := by simpa [this] using hb
    have : (toySchemaToSchema T).R 0 = 0 := Nat.eq_of_le_of_ge this (Nat.zero_le _)
    have : c = 0 := Nat.eq_of_le_of_lt_succ h0 (by simpa [this])
    cases Nat.ne_of_gt (Nat.succ_pos c) (by simpa [this])

end ALSTAR
