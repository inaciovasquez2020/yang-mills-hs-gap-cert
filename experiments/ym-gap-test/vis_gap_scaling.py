import numpy as np
import matplotlib.pyplot as plt

L = np.array([16,32,64,128,256], dtype=float)
lam = np.array([0.0340538006,0.0090561549,0.0023355463,0.0005930603,0.0001494267], dtype=float)

plt.figure()
plt.loglog(L, lam, marker="o", linestyle="-")
plt.loglog(L, 8.0/(L**2), linestyle="--")
plt.xlabel("L")
plt.ylabel("lambda_min(L)")
plt.title("lambda_min scaling: data vs 8/L^2")
plt.tight_layout()
plt.savefig("vis_gap_scaling.png", dpi=200)
print("wrote vis_gap_scaling.png")
