# Canonical Missing Object

Status: OPEN

Canonical blocker:
`BLOCK_SPECTRAL_GAP_CORE_LEMMA`

Statement:
For every block \(B\) of side \(L\),
\[
\sup_U \|\nabla^2 S_B(U)-\beta \Delta_B\| \le C L^{-2}.
\]

Equivalent forms:
1. \(\lambda_{\min}(\nabla^2 S_B(U)) \ge c L^{-2}\)
2. \(\gamma_B \ge c L^{-2}\)
3. \(\operatorname{Var}_B(f) \le C L^2 \sum_\ell \|\nabla_\ell f\|^2\)

Dependency role:
`YM-1 -> YM-2 -> BLOCK_SPECTRAL_GAP_CORE_LEMMA -> SPECTRAL_CONTRACTION_RG -> YM_MASS_GAP_ROUTE_CERTIFICATE_2026`

Normalization rule:
No status file may declare a weaker or earlier blocker than `BLOCK_SPECTRAL_GAP_CORE_LEMMA`.
