import json
from pathlib import Path
import numpy as np

def schatten_p_witness(vals, p: float, N: int):
    vals = np.asarray(vals, dtype=float)
    vals = np.sort(np.abs(vals))[::-1]
    vals = vals[: min(N, len(vals))]
    if len(vals) == 0:
        return 0.0
    return float(np.sum(vals ** p) ** (1.0 / p))

def build_mock_spectrum(L: int, cutoff: int, m0: float, seed: int = 0):
    rng = np.random.default_rng(seed)
    base = np.arange(1, cutoff + 1, dtype=float)
    decay = 1.0 / ((base + m0) ** 0.75)
    noise = 0.02 * rng.standard_normal(cutoff)
    vals = np.maximum(decay + noise, 1e-12)
    return vals

def main():
    outdir = Path("data/schatten_witness")
    outdir.mkdir(parents=True, exist_ok=True)

    rows = []
    for L, cutoff, m0 in [(8, 64, 0.8), (12, 96, 0.8), (16, 128, 0.8)]:
        vals = build_mock_spectrum(L=L, cutoff=cutoff, m0=m0, seed=L + cutoff)
        rec = {
            "L": L,
            "cutoff": cutoff,
            "m0": m0,
            "W_3_N32": schatten_p_witness(vals, p=3.0, N=32),
            "W_4_N32": schatten_p_witness(vals, p=4.0, N=32),
            "W_6_N32": schatten_p_witness(vals, p=6.0, N=32),
            "W_3_N64": schatten_p_witness(vals, p=3.0, N=64),
            "W_4_N64": schatten_p_witness(vals, p=4.0, N=64),
            "W_6_N64": schatten_p_witness(vals, p=6.0, N=64),
        }
        rows.append(rec)

    outfile = outdir / "schatten_p_witness.json"
    outfile.write_text(json.dumps(rows, indent=2))
    print(f"wrote {outfile}")

if __name__ == "__main__":
    main()
