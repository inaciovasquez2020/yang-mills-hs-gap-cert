import ALSTAR.Axioms.Rayleigh
import Mathlib.LinearAlgebra.FiniteDimensional

namespace ALSTAR

/-
Restricted replacement program:

Goal: replace `pulse_logbound_implies_lambdaMin_zero` by a theorem in stages:

Stage FD-1:
  Assume [FiniteDimensional ℝ H] and Q is symmetric/self-adjoint with discrete spectrum.
  Prove:
    (∃ sequence x_k ⟂ ker Q, ‖x_k‖=1, ⟪x_k,Q x_k⟫→0) → lambdaMinPhys=0.

Stage FD-2:
  Prove existence of such a sequence from your concrete PulseBound + LogBound hypotheses
  in a finite-dimensional toy Hamiltonian model.

Stage FD-3:
  Lift FD-2 from toy model to the actual YM operator class (Balaban/OS framework),
  replacing finite-dimensionality by compactness / localization + tightness.
-/

end ALSTAR
