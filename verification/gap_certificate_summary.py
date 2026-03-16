import json
import numpy as np
from pathlib import Path

gap_file = Path("data/gap_scaling/gap_scaling.json")

with open(gap_file) as f:
    data = json.load(f)

L = np.array([d["L"] for d in data], dtype=float)
gap = np.array([d["gap"] for d in data], dtype=float)

min_gap = float(np.min(gap))
max_gap = float(np.max(gap))
mean_gap = float(np.mean(gap))

summary = {
    "volumes": L.tolist(),
    "gaps": gap.tolist(),
    "min_gap": min_gap,
    "max_gap": max_gap,
    "mean_gap": mean_gap
}

print("Gap summary")
print("min_gap =", min_gap)
print("max_gap =", max_gap)
print("mean_gap =", mean_gap)

Path("reports").mkdir(exist_ok=True)

with open("reports/gap_certificate_summary.json","w") as f:
    json.dump(summary,f,indent=2)
