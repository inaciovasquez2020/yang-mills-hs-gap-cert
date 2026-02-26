import numpy as np

def blurred_cmi(beta, eps):
    return np.exp(-eps) * np.exp(-beta)

betas = np.linspace(0, 6, 25)
epsilons = [0.0, 0.5, 1.0, 2.0]

for eps in epsilons:
    print(f"\nEPS={eps}")
    for b in betas:
        I = blurred_cmi(b, eps)
        print(f"beta={b:4.2f}  I_blurr={I:.12e}")
