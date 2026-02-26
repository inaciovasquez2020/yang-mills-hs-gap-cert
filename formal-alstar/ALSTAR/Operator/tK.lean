import ALSTAR.Specs.PulseBridgeSpec

namespace ALSTAR

structure tK {α : Type u} (A : Schema α) : Prop :=
  (dyson_trunc :
    ∀ Λ : Nat, True)
  (rayleigh_extract :
    True)
  (rg_stability :
    True)
  (spectral_collapse :
    lambdaMin A = 0)

end ALSTAR
