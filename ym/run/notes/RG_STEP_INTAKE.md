To instantiate the RG one-step inequality numerically:

1) Export finite-volume proxies for H_Λ and H_{Λ/b} as matrices:
   run/data/H_Lambda.npy
   run/data/H_Lambda_over_b.npy

2) Run:
   python3 run/scripts/rg_step_bound_from_matrices.py --H run/data/H_Lambda.npy --Hb run/data/H_Lambda_over_b.npy
