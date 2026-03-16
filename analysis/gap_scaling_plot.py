import json
import numpy as np
import matplotlib.pyplot as plt

with open("data/gap_scaling/gap_scaling.json") as f:
    data = json.load(f)

L = np.array([d["L"] for d in data], dtype=float)
gap = np.array([d["gap"] for d in data], dtype=float)

# fit model gap(L) ≈ a + b/L
X = np.vstack([np.ones_like(L), 1.0/L]).T
a, b = np.linalg.lstsq(X, gap, rcond=None)[0]

Lfit = np.linspace(min(L), max(L), 200)
gapfit = a + b / Lfit

plt.scatter(L, gap, label="measured gap")
plt.plot(Lfit, gapfit, label="fit a + b/L")
plt.xlabel("Lattice size L")
plt.ylabel("Spectral gap")
plt.title("Finite-volume spectral gap scaling")
plt.legend()

plt.savefig("figures/gap_scaling.png", dpi=300)
print("saved figures/gap_scaling.png")

with open("reports/gap_scaling_report.txt","w") as f:
    f.write("Finite-volume gap scaling analysis\n")
    f.write(f"a (infinite-volume estimate) = {a}\n")
    f.write(f"b coefficient = {b}\n")

print("saved reports/gap_scaling_report.txt")
