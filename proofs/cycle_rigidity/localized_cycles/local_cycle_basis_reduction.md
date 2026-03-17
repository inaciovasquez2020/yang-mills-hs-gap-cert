# Local Cycle Basis Reduction

Under the global localization criterion

support(Φ(γ)) ⊂ B_R(v)

every admissible cycle class lies in the local subgraph H = G[B_R(v)].

Hence the relevant cycle space satisfies

Z1^loc(G;R) = sum_v Z1(B_R(v)).

For each center v:
1. choose a spanning tree T_v of B_R(v)
2. for each non-tree edge e, form the fundamental cycle
   γ_e = e ∪ P_{T_v}(e)

These fundamental cycles form a basis of Z1(B_R(v)).

Therefore

dim Z1(B_R(v)) = |E(B_R(v))| - |V(B_R(v))| + 1

and the admissible localized cycle complexity is bounded locally.
