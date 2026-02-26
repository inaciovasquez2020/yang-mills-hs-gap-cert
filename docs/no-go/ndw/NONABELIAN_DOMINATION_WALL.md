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

## GOE restricted-regime tests (finite groups)

Reproducible exact-enumeration tests:
- docs/no-go/tests/goe/goe_finite_group_exact.py
  Computes I(Past;Future|Boundary) for a tiny reflection-symmetric lattice with:
  * Z2 (abelian sanity)
  * S3 (nonabelian SU(2)-truncation proxy)
  using a heat-kernel-type plaquette weight exp(beta * chi2(g_p)).

- docs/no-go/tests/goe/goe_refute_search.py
  Grid-searches beta for near-vanishing I(P;F|B) in the S3 model.

These tests are interface probes for GOE (not proofs).
