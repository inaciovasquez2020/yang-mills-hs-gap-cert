# Valuation Additivity — Proof Shell

## Target
Replace `axiom valuation_additivity` in `YMFormal/AnchoredClosure.lean` by a theorem.

## First missing lemma
```lean
lemma carrier_union_law
    (P Q : AnchoredPatch)
    (hdisj : Disjoint (carrier P) (carrier Q)) :
    carrier (merge P Q) = carrier P ∪ carrier Q
Reduction chain
carrier_union_law
→ valuation_on_disjoint_union
→ valuation_additivity
Obligations
Define merge : AnchoredPatch → AnchoredPatch → AnchoredPatch.
Prove support compatibility of merge.
Prove carrier disjoint-union formula.
Push valuation through finite union normalization.
Conclude valuation_additivity.
