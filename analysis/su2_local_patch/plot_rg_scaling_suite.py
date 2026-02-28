import json, argparse
import numpy as np
import matplotlib.pyplot as plt

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--infile", type=str, required=True)
    ap.add_argument("--outpng", type=str, default="analysis/su2_local_patch/results/rg_scaling_suite.png")
    args = ap.parse_args()

    with open(args.infile, "r") as f:
        data = json.load(f)

    Ls = sorted([int(k) for k in data["per_L"].keys()])
    gl = []
    gls = []
    gt = []
    gts = []

    for L in Ls:
        agg = data["per_L"][str(L)]["agg"]
        gl.append(agg["gamma_lap"]["mean"])
        gls.append(agg["gamma_lap"]["std"])
        gt.append(agg["gamma_tr"]["mean"])
        gts.append(agg["gamma_tr"]["std"])

    Ls = np.array(Ls, dtype=float)
    gl = np.array(gl, dtype=float)
    gt = np.array(gt, dtype=float)
    gls = np.array(gls, dtype=float)
    gts = np.array(gts, dtype=float)

    plt.figure()
    plt.errorbar(Ls, gl, yerr=gls, marker="o", linestyle="none", label="gamma_lap")
    plt.errorbar(Ls, gt, yerr=gts, marker="s", linestyle="none", label="gamma_tr")
    plt.xlabel("L")
    plt.ylabel("gamma = (log gap(L/b) - log gap(L)) / log b")
    plt.legend()
    plt.tight_layout()
    plt.savefig(args.outpng, dpi=180)
    print("wrote", args.outpng)

if __name__ == "__main__":
    main()
