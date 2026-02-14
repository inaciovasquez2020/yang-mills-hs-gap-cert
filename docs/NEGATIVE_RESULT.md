Negative Result: Failure of Hilbert–Schmidt Coercivity for Yang–Mills

This repository certifies a negative result for the Yang–Mills mass gap program.

Statement
The naive approach of proving a Yang–Mills mass gap via Hilbert–Schmidt coercivity of the gauge-fixed Hessian fails. Explicit truncation-based certificates show that the Hilbert–Schmidt norm diverges monotonically with cutoff P.

Evidence
Executable certificates demonstrate:
• bounded local contributions (eta)
• monotone growth of global contributions (delta)
• divergence of eta + delta beyond the coercive threshold

Status
This failure mode is certified, CI-verified, and frozen under the tag:
frozen-ym-hs-gap-divergence

Implication
Any successful Yang–Mills mass gap proof must:
• use a stronger operator topology than Hilbert–Schmidt, or
• exploit additional algebraic, geometric, or probabilistic structure

This result eliminates an entire class of naive coercivity-based strategies.

