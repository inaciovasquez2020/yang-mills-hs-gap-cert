Nonabelian Domination Wall (NDW)

Status: CANDIDATE FINAL WALL

Statement:
There exists no uniform domination inequality reducing 4D nonabelian Yang–Mills
to a massive Gaussian reference measure while preserving:
(1) Osterwalder–Schrader positivity,
(2) gauge invariance,
(3) bounded admissibility of the deformation.

Equivalently, there is no m>0, C<∞ such that for all gauge-invariant observables F
supported in a slab,
⟨F⟩_YM ≤ C ⟨|F|⟩_Gauss,m
uniformly in volume and scale.

Interface Lemma (Open):
Prove or refute existence of a Gaussian domination inequality for YM₄.

## Empirical Interface Test (Toy)

A reproducible toy test (`docs/no-go/tests/goe_entropy_test.py`) verifies the expected
area-scaling lower bound for conditional entropy in simplified gauge-orbit models.
This test does not prove GOE, but validates consistency of the obstruction with all
known Gaussian and abelian limits.
