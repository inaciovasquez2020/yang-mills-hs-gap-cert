# Helly-Type Overlap Lemma

The previous chain-length lemma is false under pairwise overlap control alone.

Counterexample:
a chain of overlapping blocks may have arbitrary length while
all consecutive intersections are nonempty and no global overlap exists.

## Corrected hypothesis

Assume lattice blocks of side length L satisfy

1. B_i ∩ B_{i+1} ≠ ∅ for all i
2. ⋂_{i=1}^k B_i ≠ ∅
3. ⋃_{i=1}^k B_i ⊂ B_R(v) for some v

Then the chain is localized in a single radius-R region.

## Corrected rigidity statement

Any deterministic cycle-rigidity statement must use a global localization
hypothesis stronger than bounded-radius local homogeneity or pairwise overlap
diameter bounds alone.
