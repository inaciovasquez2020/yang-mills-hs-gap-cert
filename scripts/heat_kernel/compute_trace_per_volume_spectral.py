import json
from pathlib import Path
import numpy as np
import scipy.sparse.linalg as spla
from tests.spectral_wall.spectral_gap_radial import build_operator
from scipy.sparse.linalg import ArpackNoConvergence

A = build_operator(d=4, k=1, ell=0, n=800)

r = 8
t = 0.1

try:
    vals = spla.eigsh(
        A,
        k=r,
        which="SA",
        tol=1e-6,
        maxiter=400000,
        return_eigenvectors=False
    )
except ArpackNoConvergence as e:
    vals = e.eigenvalues

vals = np.sort(vals)
trace_lb = float(np.sum(np.exp(-t * vals)) / A.shape[0])

out = {
    "operator": "reduced_radial_S4",
    "d": 4,
    "k": 1,
    "ell": 0,
    "n": int(A.shape[0]),
    "t": t,
    "eigenvalues_used": vals.tolist(),
    "trace_per_volume_lower_bound": trace_lb,
    "method": "finite-spectrum lower bound",
    "status": "numerical_witness_only"
}

Path("data/heat_kernel").mkdir(parents=True, exist_ok=True)
Path("data/heat_kernel/trace_per_volume_spectral_lb.json").write_text(
    json.dumps(out, indent=2)
)

print(out)
