import numpy as np
from fit_two_plaquette_k24 import grid_search

print("\n" + "="*70)
print("ROBUST TWO-PLAQUETTE FIT ANALYSIS")
print("="*70)
print("Testing multiple seeds and sample sizes to find worst-case C1")
print("-"*70)

for n in [320, 400, 520, 700]:
    worst_C1 = -np.inf
    best_seed = None
    best_C2 = None
    results = []
    
    print(f"\n{'='*60}")
    print(f"Sample size n = {n}")
    print(f"{'='*60}")
    
    for seed in range(5):  # Test 5 seeds for each n
        try:
            C1, C2 = grid_search(n=n, k=24, seed=seed, C2max=20.0, m=41)
            results.append((seed, C1, C2))
            print(f"  seed={seed:2d}: C1={C1:+.6f}, C2={C2:.2f}")
            
            if C1 > worst_C1:
                worst_C1 = C1
                best_seed = seed
                best_C2 = C2
        except Exception as e:
            print(f"  seed={seed:2d}: failed - {e}")
    
    # Statistics
    if results:
        C1_vals = [r[1] for r in results]
        print(f"\n  Summary for n={n}:")
        print(f"    mean C1 = {np.mean(C1_vals):+.6f}")
        print(f"    std C1  = {np.std(C1_vals):.6f}")
        print(f"    min C1  = {np.min(C1_vals):+.6f}")
        print(f"    max C1  = {np.max(C1_vals):+.6f}")
        print(f"  → worst C1 = {worst_C1:+.6f} (seed={best_seed}, C2={best_C2:.2f})")
