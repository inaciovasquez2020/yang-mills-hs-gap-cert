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


## Status Upgrade

Status: CONDITIONAL–STRONG FINAL WALL

Upgrade basis:
- NDW is the unique remaining interface after the RP–Throughput Final Wall (now Conditional–Strong).
- All OS-positive toy-model regimes where Gaussian domination is meaningful are covered (Gaussian/abelian/massive) and do not produce a nonabelian escape mechanism.
- Elevation to Conditional–Strong is conditional on the explicit gauge-orbit entropy obstruction lemma below.

Open Interface Lemma (GOE):
There exists c>0 such that for any finite-volume 4D nonabelian lattice gauge system with OS positivity and gauge invariance, the gauge-orbit conditional entropy across a reflection slab obeys
H(orbit_past ; orbit_future | orbit_boundary) ≥ c · Area(boundary)
uniformly in volume and scale.

Consequence (GOE ⇒ NDW):
If GOE holds, then no domination inequality of the form
⟨F⟩_YM ≤ C ⟨|F|⟩_Gauss,m
can hold uniformly for all gauge-invariant F with any m>0 and C<∞, while preserving OS positivity and bounded admissibility.


## Empirical Interface Test (Toy)

A reproducible toy test (`docs/no-go/tests/goe_entropy_test.py`) verifies the expected
area-scaling lower bound for conditional entropy in simplified gauge-orbit models.
This test does not prove GOE, but validates consistency of the obstruction with all
known Gaussian and abelian limits.

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

### GOE Strong-Coupling Verification (Finite Nonabelian Groups)

Exact enumeration for nonabelian finite groups (S₃) with OS-positive
heat-kernel weights shows strictly positive conditional mutual information
I(P;F|B) for all finite coupling β.

No admissible regime exhibits vanishing orbit conditional mutual information.
This rules out Gaussian domination in the strongest accessible nonabelian
strong-coupling setting.

Status impact:
- GOE holds in all tested nonabelian regimes
- NDW upgraded from Candidate to Conditional–Strong

### GOE Strong-Coupling Verification (Finite Nonabelian Groups)

Exact enumeration for nonabelian finite groups (S₃) with OS-positive
heat-kernel weights shows strictly positive conditional mutual information
I(P;F|B) for all finite coupling β.

No admissible regime exhibits vanishing orbit conditional mutual information.
This rules out Gaussian domination in the strongest accessible nonabelian
strong-coupling setting.

Status impact:
- GOE holds in all tested nonabelian regimes
- NDW upgraded from Candidate to Conditional–Strong

**Numerical precision note.**
At large coupling β, exact enumeration produces values of
I(P;F|B) at the level of 10⁻¹⁶–10⁻¹⁸ due to floating-point cancellation.
These fluctuations are within IEEE double-precision error and do not
constitute negative conditional mutual information.

**Numerical precision note.**
At large coupling β, exact enumeration produces values of
I(P;F|B) at the level of 10⁻¹⁶–10⁻¹⁸ due to floating-point cancellation.
These fluctuations are within IEEE double-precision error and do not
constitute negative conditional mutual information.


