Mourre commutator bound derivation plan

Target
i[H_ren, A] >= c0 L - C0 1 with c0 > 0 uniform in cutoff

Objects
H_ren = H_E + H_B + V_ct
L = H_E + H_B
A = dilation generator on the spatial lattice or continuum limit proxy

Milestones
M1 Define A on lattice Hilbert space and specify core domain D
M2 Prove H_ren is of class C^1(A) on D
M3 Compute i[H_E, A] and i[H_B, A] and isolate positive term 2L
M4 Bound i[V_ct, A] in operator norm by C0 independent of cutoff
M5 Control boundary and discretization errors uniformly in cutoff
M6 Localize with IMS and obtain uniform Mourre estimate on spectral window I

Deliverables
mourre_analysis/derivations/commutator_calculus.md
mourre_analysis/lemmas/Lem_Mourre_C1.json
mourre_analysis/lemmas/Lem_Mourre_PositiveFree.json
mourre_analysis/lemmas/Lem_Mourre_BoundedPerturb.json
mourre_analysis/tests/test_mourre_sanity.py
