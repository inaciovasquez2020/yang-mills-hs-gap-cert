# Simulated Mass-Gap Proof Certificate

## Status
SIMULATED

## Model
Abelianized Wilson–Hessian surrogate on a 2D discrete torus

## Parameters
- lattice size: 8
- mass parameter: 0.75
- coupling parameter: 1.25
- RG steps: 6
- RG scale floor: 0.9
- RG shift floor: 0.01

## Formal simulated statement
For H_n = m I + beta Δ_torus with m > 0 and beta >= 0, the exact spectral gap is lambda_min(H_n) = m. Under any RG update g -> a g + b with a >= a_min > 0 and b >= 0, positivity persists and the gap remains >= a_min^s m after s steps.

## Exact finite-volume gap
\[
\lambda_{\min}(H_n) = 0.750000000000
\]

## RG-protected lower bound
\[
g_{\mathrm{RG}} \ge 0.626877073161
\]

## Lowest spectral modes
| mode | Laplacian eigenvalue | Hessian eigenvalue |
|---|---:|---:|
| (0,0) | 0.000000000000 | 0.750000000000 |
| (0,1) | 0.585786437627 | 1.482233047034 |
| (1,0) | 0.585786437627 | 1.482233047034 |
| (0,7) | 0.585786437627 | 1.482233047034 |
| (7,0) | 0.585786437627 | 1.482233047034 |
| (1,1) | 1.171572875254 | 2.214466094067 |
| (1,7) | 1.171572875254 | 2.214466094067 |
| (7,1) | 1.171572875254 | 2.214466094067 |
| (7,7) | 1.171572875254 | 2.214466094067 |
| (0,2) | 2.000000000000 | 3.250000000000 |
| (2,0) | 2.000000000000 | 3.250000000000 |
| (0,6) | 2.000000000000 | 3.250000000000 |

## RG chain
| step | scale factor | additive shift | incoming gap | outgoing lower bound |
|---:|---:|---:|---:|---:|
| 1 | 0.928346868943 | 0.001812692469 | 0.750000000000 | 0.698072844176 |
| 2 | 0.948658288097 | 0.003296799540 | 0.698072844176 | 0.665529388863 |
| 3 | 0.963212055883 | 0.004511883639 | 0.665529388863 | 0.645557814536 |
| 4 | 0.973640286188 | 0.005506710359 | 0.645557814536 | 0.634047805655 |
| 5 | 0.981112439716 | 0.006321205588 | 0.634047805655 | 0.628393395091 |
| 6 | 0.986466471676 | 0.006988057881 | 0.628393395091 | 0.626877073161 |

## Interpretation
This is an executable finite-dimensional surrogate certificate. It demonstrates the coercivity-transfer pattern but is not a proof of the non-abelian Yang–Mills mass gap.

## Limitations
- Finite-dimensional toy surrogate only
- Abelianized spectrum, not full non-abelian Wilson Hessian
- RG rule is imposed, not derived
- No continuum limit theorem
- No Osterwalder–Schrader reconstruction theorem is proved here
