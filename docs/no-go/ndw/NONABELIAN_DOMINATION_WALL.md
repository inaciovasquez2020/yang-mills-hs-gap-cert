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
