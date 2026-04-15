# SPECTRAL_CONTRACTION_RG — Next Missing Object

Status: OPEN

Immediate frontier:
derive the RG spectral contraction step from the block spectral gap input and expose its exact interface to the final Yang–Mills route certificate.

Canonical missing object:
a theorem-level bridge of the form

block spectral gap input
=> one-step RG spectral contraction
=> iterated contraction along the RG chain
=> certified interface to the final Yang–Mills route certificate.

Required input schema:
1. A block-scale operator or transfer object carrying the current spectral-gap hypothesis.
2. A contraction statement at the next RG scale with an explicit contraction factor.
3. Stability of the contraction under the repository's declared RG iteration regime.
4. A terminal handoff statement showing exactly which certificate field consumes the contraction output.

Required output schema:
- named theorem target for the one-step contraction;
- named corollary for RG iteration;
- named interface lemma into the final route certificate.

Non-claim:
This note does not assert that SPECTRAL_CONTRACTION_RG is proved.
It records the exact immediate theorem object now exposed by the current reduction chain.

Certificate interface:
The final Yang–Mills route certificate may only consume SPECTRAL_CONTRACTION_RG through an explicit theorem-level interface;
no implicit transfer is allowed.
