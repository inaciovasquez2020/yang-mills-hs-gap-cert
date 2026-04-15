# YM Dependency Tree (2026-04)

Status: CONDITIONAL

## Final certificate
YM_MASS_GAP_ROUTE_CERTIFICATE_2026

## Hard dependency tree

YM-1
-> YM-2
-> BLOCK_SPECTRAL_GAP_CORE_LEMMA
-> SPECTRAL_CONTRACTION_RG
-> YM_MASS_GAP_ROUTE_CERTIFICATE_2026

YM-3
-> REFLECTION_POSITIVITY_SURVIVES_BLOCKING
-> YM_MASS_GAP_ROUTE_CERTIFICATE_2026

YM-4
-> YM-5
-> YM_MASS_GAP_ROUTE_CERTIFICATE_2026

## Alternative sublemma ladder for the core lemma

Sublemma 1 — Local Hessian Approximation
Sublemma 2 — Local-to-Global Laplacian Comparison
Sublemma 3 — Spectral Transfer

(Sublemma 1 and Sublemma 2 and Sublemma 3 and explicit composition)
-> BLOCK_SPECTRAL_GAP_CORE_LEMMA

## Upgrade rule

No claim upgrade is permitted unless:
1. SPECTRAL_CONTRACTION_RG is discharged,
2. REFLECTION_POSITIVITY_SURVIVES_BLOCKING is discharged,
3. YM-4 and YM-5 are discharged,
4. and the spectral gate is closed either by the core lemma directly or by the full discharged sublemma ladder with explicit composition.
