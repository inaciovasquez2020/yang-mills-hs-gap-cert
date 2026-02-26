import math
import numpy as np
from goe_finite_group_exact import group_S3, exact_cmi_toy

def search(threshold=1e-6):
    g = group_S3()
    betas = np.linspace(0.0, 3.0, 61)
    best = (1e9, None)
    for beta in betas:
        I = exact_cmi_toy(g, float(beta))
        if I < best[0]:
            best = (I, float(beta))
        if I <= threshold:
            print(f"FOUND candidate near-vanishing CMI: beta={beta:.4f} I={I:.10f}")
            return
    print(f"MIN over grid: beta={best[1]:.4f} I={best[0]:.10f}")

if __name__ == "__main__":
    search()
