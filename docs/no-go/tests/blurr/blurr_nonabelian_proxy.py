import numpy as np

def nonabelian_blurr_cmi(beta, eps):
    return np.exp(-eps) * np.exp(-beta) + 0.01 * np.exp(-beta/2)

betas = np.linspace(0, 10, 51)
eps = 1.0

vals = []
for b in betas:
    I = nonabelian_blurr_cmi(b, eps)
    vals.append(I)
    print(f"beta={b:5.2f}  I_blurr={I:.14e}")

print("\nMIN =", min(vals))
