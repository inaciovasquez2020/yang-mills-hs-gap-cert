import argparse, numpy as np

def load(path: str) -> np.ndarray:
    if path.endswith(".npy"): return np.load(path)
    if path.endswith(".npz"):
        z = np.load(path)
        if "H" in z: return z["H"]
        if "arr_0" in z: return z["arr_0"]
        raise ValueError("npz must contain key 'H' or 'arr_0'")
    raise ValueError("supported: .npy or .npz")

def spectral_floor(H: np.ndarray, vac_index: int = 0) -> float:
    # finite-dimensional proxy: assume vacuum is eigenvector indexed by vac_index after diagonalization ordering.
    w = np.linalg.eigvalsh(H)
    w = np.sort(w)
    if len(w) <= 1: return float("nan")
    # take the first eigenvalue above the bottom (proxy for gap in finite volume)
    return float(w[1])

def op_norm(A: np.ndarray) -> float:
    # spectral norm
    return float(np.linalg.norm(A, ord=2))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--H", required=True, help="H_Lambda (.npy/.npz)")
    ap.add_argument("--Hb", required=True, help="H_{Lambda/b} (.npy/.npz)")
    args = ap.parse_args()

    H = load(args.H)
    Hb = load(args.Hb)
    V = Hb - H

    I = spectral_floor(H)
    Ib = spectral_floor(Hb)
    eps = op_norm(V)

    print(f"I(Lambda)   ~ {I}")
    print(f"I(Lambda/b) ~ {Ib}")
    print(f"eps = ||Hb-H||_op ~ {eps}")
    print(f"bound: I(Lambda/b) >= I(Lambda) - eps  =>  RHS ~ {I - eps}")
    print(f"check: Ib - (I-eps) ~ {Ib - (I - eps)}")
