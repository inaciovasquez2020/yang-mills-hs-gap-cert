To produce a concrete bound on λ2(T_Λ):

1) Export the finite-volume transfer matrix (restricted to the Wilson-plaquette channel if desired)
   as a dense numpy array T (n×n), saved to:
   run/data/T_Lambda.npy

2) Run:
   python3 run/scripts/compute_lambda2.py --T run/data/T_Lambda.npy --stochastic

Output gives λ2 and |λ2|, hence m = -log|λ2| if |λ2|<1.
