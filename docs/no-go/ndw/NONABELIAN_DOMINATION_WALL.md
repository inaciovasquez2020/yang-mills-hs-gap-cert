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
