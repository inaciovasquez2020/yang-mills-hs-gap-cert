import Mathlib.MeasureTheory.Measure.MeasureSpace

namespace YMFormal

open MeasureTheory
open Set

variable {α : Type*} [MeasurableSpace α]

/-- `SupportBound μ A` means `μ` is supported on `A`,
i.e. `μ (Aᶜ) = 0`. -/
def SupportBound (μ : Measure α) (A : Set α) : Prop :=
  μ (Aᶜ) = 0

namespace SupportBound

variable {μ : Measure α} {A B : Set α}

/-- Monotonicity of support under set enlargement. -/
theorem mono
  (hA : SupportBound μ A)
  (hAB : A ⊆ B) :
  SupportBound μ B := by
  unfold SupportBound at *
  have hsubset : Bᶜ ⊆ Aᶜ :=
    compl_subset_compl.mpr hAB
  exact measure_mono_null hsubset hA

end SupportBound

/-- Drift control: both measures supported on the same set. -/
def SupportDrift
  (μ ν : Measure α)
  (A : Set α) : Prop :=
  SupportBound μ A ∧ SupportBound ν A

namespace SupportDrift

variable {μ ν : Measure α} {A B : Set α}

/-- Monotonicity of drift under set enlargement. -/
theorem mono
  (h : SupportDrift μ ν A)
  (hAB : A ⊆ B) :
  SupportDrift μ ν B := by
  constructor
  · exact SupportBound.mono h.left hAB
  · exact SupportBound.mono h.right hAB

end SupportDrift

end YMFormal
