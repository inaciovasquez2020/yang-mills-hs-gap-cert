Stronger-Norm YM Gap Program (post HS obstruction)

Goal
Replace Hilbert–Schmidt coercivity with a topology that is:
• UV-regularized
• volume-normalized
• capable of yielding a spectral gap

Candidate norms (minimal set)
1) Heat-kernel trace-per-volume:
   b(t) = (1/Vol) Tr(exp(-t L_YM)) with quantitative decay lower bounds.

2) Schatten p per volume (p>2):
   (1/Vol) ||exp(-t L_YM)||_{S_p}^p with certified bounds.

3) Poincaré / log-Sobolev on gauge-fixed configuration space:
   certified coercivity functional ⇒ spectral gap.

Certificate interface
A certificate supplies:
• operator spec and regulator
• chosen norm family
• numerical/analytic bound "bound" with pass if bound < 1 (or equivalent)
• monotone limit argument to infinite volume
• reproducible verifier

Status
HS route is blocked (certified divergence). This plan is the minimal successor track.

