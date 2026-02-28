import Mathlib.Data.Real.Basic
universe u
namespace ALSTAR
structure Bubble (α : Type u) where
center : α
structure PackedBubbles (α : Type u) where
k : ℕ
bubbles : Fin k → Bubble α
axiom Energy {α : Type u} : Type u → Type u
axiom energy_additivity_disjoint :
True
axiom bubble_orthogonality :
True
axiom pack_linear_in_n :
True
end ALSTAR
