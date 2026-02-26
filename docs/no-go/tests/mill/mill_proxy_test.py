import numpy as np

def mill_entropy(beta):
    return 1e-3 * np.exp(-beta/3) + 1e-6

betas = np.linspace(0, 20, 200)
vals = []

for b in betas:
    I = mill_entropy(b)
    vals.append(I)
    print(f"beta={b:5.2f}  Mill_entropy={I:.12e}")

print("\nMIN =", min(vals))
