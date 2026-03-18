import json
import numpy as np
from pathlib import Path

def discrete_gradient(f):
    return np.diff(f)

def block_poincare_stats(L, trials=500, seed=0):
    rng = np.random.default_rng(seed + L)
    ratios = []
    scaled = []
    for _ in range(trials):
        f = rng.standard_normal(L)
        f = f - np.mean(f)
        grad = discrete_gradient(f)
        den = np.sum(grad**2)
        if den <= 1e-12:
            continue
        num = np.sum(f**2)
        r = num / den
        ratios.append(r)
        scaled.append(r / (L**2))
    ratios = np.array(ratios)
    scaled = np.array(scaled)
    return {
        "L": L,
        "trials": int(len(ratios)),
        "ratio_mean": float(np.mean(ratios)),
        "ratio_min": float(np.min(ratios)),
        "ratio_max": float(np.max(ratios)),
        "scaled_mean": float(np.mean(scaled)),
        "scaled_min": float(np.min(scaled)),
        "scaled_max": float(np.max(scaled)),
    }

def main():
    outdir = Path("results/block_poincare")
    outdir.mkdir(parents=True, exist_ok=True)
    data = [block_poincare_stats(L) for L in [8, 16, 32, 64, 128]]
    payload = {"block_poincare_scaling": data}
    path = outdir / "block_poincare_scaling.json"
    path.write_text(json.dumps(payload, indent=2))
    print(json.dumps(payload, indent=2))

if __name__ == "__main__":
    main()
