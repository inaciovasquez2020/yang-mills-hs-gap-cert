import argparse, numpy as np

def load_matrix(path: str) -> np.ndarray:
    if path.endswith(".npy"):
        return np.load(path)
    if path.endswith(".npz"):
        z = np.load(path)
        if "T" in z: return z["T"]
        if "arr_0" in z: return z["arr_0"]
        raise ValueError("npz must contain key 'T' or 'arr_0'")
    raise ValueError("supported: .npy or .npz")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--T", required=True, help="transfer matrix file (.npy or .npz)")
    ap.add_argument("--stochastic", action="store_true", help="assume spectral radius 1 and take 2nd largest eigenvalue magnitude")
    args = ap.parse_args()

    T = load_matrix(args.T)
    if T.ndim != 2 or T.shape[0] != T.shape[1]:
        raise ValueError("T must be square")

    w = np.linalg.eigvals(T)
    w = np.array(w, dtype=np.complex128)

    if args.stochastic:
        idx = np.argsort(-np.abs(w))
        lam1 = w[idx[0]]
        lam2 = w[idx[1]] if len(w) > 1 else 0.0
        print(f"lambda1 ~ {lam1}")
        print(f"lambda2 ~ {lam2}")
        print(f"|lambda2| = {abs(lam2)}")
    else:
        w_sorted = np.sort(np.real_if_close(w))
        print("eigenvalues (sorted):")
        for x in w_sorted:
            print(x)

if __name__ == "__main__":
    main()
