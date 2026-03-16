import json
import numpy as np
from pathlib import Path

with open("data/gap_scaling/gap_scaling.json") as f:
    data = json.load(f)

L = np.array([d["L"] for d in data],dtype=float)
gap = np.array([d["gap"] for d in data],dtype=float)

# fit gap(L) ≈ a + b/L
X = np.vstack([np.ones_like(L),1/L]).T
a,b = np.linalg.lstsq(X,gap,rcond=None)[0]

print("estimated infinite-volume gap:",a)

Path("data/mass_gap_estimate").mkdir(parents=True,exist_ok=True)

with open("data/mass_gap_estimate/mass_gap_estimate.json","w") as f:
    json.dump({"mass_gap_estimate":float(a)},f,indent=2)
