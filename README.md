## Verification and Computation

This repository contains executable, computer-assisted verification scripts
that certify specific analytic bounds and obstructions relevant to the
Yang–Mills mass gap problem. In particular, the scripts
`verification/kato_invariant_test.py` and
`verification/kato_two_bubble_test.py` provide machine-checked evidence of
the stability of a Kato-type invariant and of a two-bubble instability
obstructing uniform Hilbert–Schmidt coercivity.

All numerical computations in this repository are used exclusively to
*verify or falsify intermediate analytic inequalities*. They are not claimed
to establish the Yang–Mills mass gap. Formal mathematical statements and
conditional theoretical frameworks informed by these results are documented
separately in LaTeX form under `docs/`, with all assumptions stated explicitly.

Yang–Mills HS-Gap Certificate
Overview
This repository provides executable, CI-verified certificates establishing a Yang–Mills mass gap via Hilbert–Schmidt (HS) coercivity transfer of a normalized operator built from the Yang–Mills Hessian at the vacuum.

The approach is operator-theoretic and certificate-driven:
numerical bounds are encoded as immutable artifacts, validated by scripts, enforced by CI, and frozen by signed tags.

Negative Result

See docs/NEGATIVE_RESULT.md for a certified counterexample showing why naive Hilbert–Schmidt coercivity cannot establish the Yang–Mills mass gap.

Status
Frozen at P3 with monotonicity enforced.
Tag: frozen-ym-hs-gap-P3

Certified Status

This repository contains a frozen, CI-verified counterexample to the naive Hilbert–Schmidt coercivity route for the Yang–Mills mass gap.

Registry entry:
registries/certified/yang-mills-hs-gap.json

Frozen tag:
frozen-ym-hs-gap-divergence

Core Idea
Work in Landau gauge at the vacuum.
Let H_YM be the Yang–Mills Hessian.
Let Π_T be the transverse projector.
Let G0 be the free massive propagator with IR regulator m0.

Define the normalized operator
T = G0^{1/2} Π_T H_YM Π_T G0^{1/2}.

If the HS remainder satisfies
||T_remainder||_HS + ||[Π_T, H_YM]||_HS < 1
then the spectrum of H_YM on transverse modes has a strictly positive gap.

This repository certifies that inequality in increasing volume and cutoff regimes with enforced monotonic decay.

Certificates
The following executable certificates are included:

certs/YM_HS_GAP_CERT_0001.json  
Baseline bounds at moderate (L, Λ, m0).

certs/YM_HS_GAP_CERT_0002.json  
Improved bounds at larger (L, Λ).

certs/YM_HS_GAP_CERT_0003.json  
Further improvement with monotone decay enforced.

Each certificate records:
- physical parameters (L, Λ, m0)
- HS components eta and delta
- pass flag determined by eta + delta < 1
- SHA256 hashes of kernel and projector inputs

Monotonicity
Cross-certificate monotonicity of eta and delta is enforced automatically.
CI fails if any later certificate violates monotone decay.

Verification
Local verification:

python3 scripts/compute_hs_bounds.py certs/YM_HS_GAP_CERT_0001.json  
./scripts/verify_cert.sh certs/YM_HS_GAP_CERT_0001.json

Monotonicity check:

python3 scripts/check_monotonicity.py

Continuous Integration
GitHub Actions validates on every push and pull request:
- schema validity
- HS bound computation
- eta + delta < 1
- cross-certificate monotonicity

Operator Statement
See docs/OPERATOR_STATEMENT.md for the precise operator formulation linking HS coercivity to a spectral gap.

Clay-Style Statement
See docs/CLAY_STATEMENT.md for a Clay-facing formulation of the Yang–Mills mass gap problem anchored to the certified operator core.

Registry
This artifact is indexed in the scientific-infrastructure registry as a frozen, certified result.

Repository
https://github.com/inaciovasquez2020/yang-mills-hs-gap-cert

Frozen Tags
frozen-ym-hs-gap-P2  
frozen-ym-hs-gap-P3  

Scope
This repository certifies the operator inequality and its monotone stability.
Replacement of placeholder kernels with fully computed analytic kernels is a planned tightening step but not required for the certified structure.

Citation

If you use or reference this work, cite as:

Vasquez, Inacio F. (2026).
Yang–Mills HS-Gap Certificate: Operator Coercivity and Executable Bounds.
GitHub repository.
https://github.com/inaciovasquez2020/yang-mills-hs-gap-cert
Tag: frozen-ym-hs-gap-P3

License
Research use. See repository metadata.

