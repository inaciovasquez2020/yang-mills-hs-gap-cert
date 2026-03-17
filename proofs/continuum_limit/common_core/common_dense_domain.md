# Common Dense Domain

Goal

Construct a common dense domain D for the renormalized quadratic forms

q_L(f) = <f, \widetilde H_L f>

such that

1. D is independent of L
2. q_L(f) is well-defined for all f in D
3. sup_L q_L(f) < \infty on controlled test vectors
4. q_L(f) -> q_\infty(f)

Prototype choice

Take D_fin to be the finitely supported cylinder functions on the lattice field
configuration space.

Required proof obligations

1. D_fin is dense in the ambient Hilbert space
2. D_fin is contained in the form domain of every \widetilde H_L
3. q_L restricted to D_fin converges pointwise
4. q_\infty on D_fin is closable
