# RPD Status Dashboard (2026-04)

## Non-claim
This file is a status dashboard only.
No proof claim is made here.

## Layer completion
- registry layer: present
- proof-shell layer: present
- theorem-target layer: present
- manifest layer: present
- proof layer: open

## Open theorem targets
- RPD-4
- RPD-5a
- RPD-5b
- RPD-6
- RPD-Error-Gain-Lemma

## Dependency chain
\[
\text{RPD-Error-Gain-Lemma}
\Longrightarrow
|E_B(U;f)|\le C' L^{-2}\|f\|^2
\Longrightarrow
\lambda_{\min}\!\left(\nabla^2S_B(U)\mid(\ker\Delta_B)^\perp\right)
\ge
\beta\lambda_1(\Delta_B)-C' L^{-2}
\]
\[
\lambda_1(\Delta_B)\ge c_\Delta L^{-2},\ \beta c_\Delta>C'
\Longrightarrow
\gamma_B\ge (\beta c_\Delta-C')L^{-2}.
\]

## Axiom map
- REFLECTION_POSITIVITY_SURVIVES_BLOCKING -> RPD-4
- pulse_logbound_implies_lambdaMin_zero -> RPD-5a
- pulse_logbound_implies_noncoercive_target -> RPD-5b
- two_bubble_log_locality_incompatible -> RPD-6

## Authoritative status boundary
Repository status is not upgraded by this dashboard.
