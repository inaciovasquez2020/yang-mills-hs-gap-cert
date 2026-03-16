import numpy as np
import json
from pathlib import Path

def spectral_gap(A):
    vals = np.linalg.eigvalsh(A)
    vals = np.sort(vals)[::-1]
    return float(vals[0] - vals[1])

def generate_operator(n):
    A = np.random.randn(n,n)
    return A.T @ A

def main():
    out = []
    for L in [16,32,64,128]:
        A = generate_operator(L)
        gap = spectral_gap(A)
        out.append({"L":L,"gap":gap})

    Path("data/gap_scaling").mkdir(parents=True,exist_ok=True)
    with open("data/gap_scaling/gap_scaling.json","w") as f:
        json.dump(out,f,indent=2)

    for r in out:
        print("L=",r["L"],"gap=",r["gap"])

if __name__ == "__main__":
    main()
