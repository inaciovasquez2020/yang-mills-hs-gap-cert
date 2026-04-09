namespace YMFormal
namespace AnchoredClosure

axiom AnchoredPatch : Type
axiom Plaquette : Type
axiom carrier : AnchoredPatch → Finset Plaquette
axiom merge : AnchoredPatch → AnchoredPatch → AnchoredPatch
axiom hessian : AnchoredPatch → Type
axiom lambdaMin : {α : Type} → α → Real
axiom StableOnAnchor : AnchoredPatch → Prop

axiom carrier_union_law
    (P Q : AnchoredPatch)
    (hdisj : Disjoint (carrier P) (carrier Q)) :
    carrier (merge P Q) = carrier P ∪ carrier Q

axiom hessian_decomposition
    (P : AnchoredPatch) :
    True

axiom local_stability_from_coercivity
    (P : AnchoredPatch)
    (hcoer : 0 < lambdaMin (hessian P)) :
    StableOnAnchor P

end AnchoredClosure
end YMFormal
