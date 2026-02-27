Title: Deterministic (Harmonic-Analysis) Route to Axiom M

Goal
Prove Dobrushin contraction (Axiom M) for the blocked vortex measure by showing that the blocked plaquette variable, after half-space Haar gauge averaging, becomes close to Haar on SU(2) at an exponential rate in block size M.

Abstract objects
Let mu_{M,U} be the distribution on SU(2) of the blocked plaquette matrix B_b(g · U) under Haar-distributed gauge transformations g supported in the half-space (with local action). For each background U, define the class function
  f_{M,U}(h) = density of mu_{M,U} w.r.t. Haar (if it exists), else interpret in L^2 sense.

Required analytic inequality (Convolution spectral gap)
There exist constants C>0 and rho in (0,1) such that for all U and all M:
  || mu_{M,U} - Haar ||_{TV} <= C rho^M.

Sufficient condition (spectral gap of the convolution operator)
If the single-step kernel K_1 induced by one local gauge averaging step defines a Markov operator P on L^2(SU(2)) with
  ||P|_{L^2_0}|| <= rho < 1,
uniformly in U, then by iteration:
  ||P^M|_{L^2_0}|| <= rho^M
and hence (by L^2->TV on compact groups) the desired TV bound holds.

Influence bound from TV closeness
Define vortex indicator v = 1{Tr(h) < 0}. For any two backgrounds U,U' differing on one fine plaquette in the block:
  | P_g(Tr(B_b(g·U))<0) - P_g(Tr(B_b(g·U'))<0) |
  <= || mu_{M,U} - mu_{M,U'} ||_{TV}
  <= || mu_{M,U} - Haar ||_{TV} + || mu_{M,U'} - Haar ||_{TV}
  <= 2 C rho^M.

Thus for |p-q| within interaction range:
  c_{p,q} <= 2 C rho^M,
and summing over q gives
  alpha <= N(M) * 2 C rho^M,
where N(M) is the number of plaquettes in range.
If N(M) is polynomial in M, then alpha < 1 for all sufficiently large M.

Status
This file records the exact missing analytic object:
  uniform spectral gap rho<1 for the induced SU(2) averaging operator.
