# QLS Local Cycle Bound

Assumptions

1. G is a lattice block-intersection graph
2. diam(γ_i ∩ γ_j) ≤ R

Then admissible cycles satisfy

supp(Φ(γ)) ⊂ B_R(v)

Cycle space inside a ball

dim Z1(B_R(v)) = |E| - |V| + 1

Degree bound Δ implies

|V(B_R(v))| ≤ 1 + Δ + Δ^2 + ... + Δ^R

Thus

|Z1(B_R(v))| = O(Δ^{R+1})

Hence

C_R(G) ≤ O(Δ^{R+1})
