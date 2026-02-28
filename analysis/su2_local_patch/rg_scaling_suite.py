import json, gc, argparse
import numpy as np

from analysis.su2_local_patch.laplacian_gap_after_blocking import (
    make_random_U, thermalize_metropolis,
    build_W_from_links, laplacian_gap,
)
from analysis.su2_local_patch.transfer_gap_after_blocking import (
    time_transfer_matrix, transfer_gap,
)
from analysis.su2_local_patch.blocking_4d import block_weighted_covariant_4d

def one_seed(L:int, b:int, beta:float, sweeps:int, eps:float, kappa:float, seed:int, alpha_override:float=0.0):
    U = make_random_U(L, 0)
    U, acc = thermalize_metropolis(U, L, beta, sweeps=sweeps, eps=eps, seed=seed)

    W0 = build_W_from_links(U, L, kappa=kappa)
    gapL = float(laplacian_gap(W0))

    T0 = time_transfer_matrix(U, L, kappa=kappa)
    tgapL = float(transfer_gap(T0))

    Uc = block_weighted_covariant_4d(U, L, b, beta, alpha_override=alpha_override)
    Lc = L // b

    W1 = build_W_from_links(Uc, Lc, kappa=kappa)
    gapLb = float(laplacian_gap(W1))

    T1 = time_transfer_matrix(Uc, Lc, kappa=kappa)
    tgapLb = float(transfer_gap(T1))

    gamma_lap = float((np.log(gapLb) - np.log(gapL)) / np.log(b)) if (gapL > 0 and gapLb > 0) else float("nan")
    gamma_tr  = float((np.log(tgapLb) - np.log(tgapL)) / np.log(b)) if (tgapL > 0 and tgapLb > 0) else float("nan")

    del U, Uc, W0, W1, T0, T1
    gc.collect()

    return {
        "L": L, "b": b, "beta": beta, "sweeps": sweeps, "eps": eps, "kappa": kappa,
        "seed": seed, "alpha_override": alpha_override,
        "accept": float(acc),
        "gapL": gapL, "gapLb": gapLb, "gamma_lap": gamma_lap,
        "tgapL": tgapL, "tgapLb": tgapLb, "gamma_tr": gamma_tr,
        "ratio_lap": float(gapLb/gapL) if gapL > 0 else float("nan"),
        "ratio_tr": float(tgapLb/tgapL) if tgapL > 0 else float("nan"),
    }

def aggregate(rows):
    def stats(key):
        xs = np.array([r[key] for r in rows], dtype=float)
        xs = xs[np.isfinite(xs)]
        if xs.size == 0:
            return {"n": 0, "mean": float("nan"), "std": float("nan"), "min": float("nan"), "max": float("nan")}
        return {"n": int(xs.size), "mean": float(xs.mean()), "std": float(xs.std(ddof=1) if xs.size > 1 else 0.0),
                "min": float(xs.min()), "max": float(xs.max())}
    return {
        "accept": stats("accept"),
        "gamma_lap": stats("gamma_lap"),
        "gamma_tr": stats("gamma_tr"),
        "ratio_lap": stats("ratio_lap"),
        "ratio_tr": stats("ratio_tr"),
        "gapL": stats("gapL"),
        "gapLb": stats("gapLb"),
        "tgapL": stats("tgapL"),
        "tgapLb": stats("tgapLb"),
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--Ls", type=str, default="6,8,10,12")
    ap.add_argument("--b", type=int, default=2)
    ap.add_argument("--beta", type=float, default=2.3)
    ap.add_argument("--sweeps", type=int, default=6)
    ap.add_argument("--eps", type=float, default=0.25)
    ap.add_argument("--kappa", type=float, default=1.0)
    ap.add_argument("--alpha_override", type=float, default=0.0)
    ap.add_argument("--seeds", type=str, default="1,2,3,4,5")
    ap.add_argument("--out", type=str, default="analysis/su2_local_patch/results/rg_scaling_suite.json")
    args = ap.parse_args()

    Ls = [int(x) for x in args.Ls.split(",") if x.strip()]
    seeds = [int(x) for x in args.seeds.split(",") if x.strip()]

    out = {"config": vars(args), "per_L": {}}

    for L in Ls:
        rows = []
        for sd in seeds:
            rows.append(one_seed(L, args.b, args.beta, args.sweeps, args.eps, args.kappa, sd, args.alpha_override))
        out["per_L"][str(L)] = {"rows": rows, "agg": aggregate(rows)}

    with open(args.out, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)

    print("wrote", args.out)
    for L in Ls:
        agg = out["per_L"][str(L)]["agg"]
        print("L", L,
              "gamma_lap", agg["gamma_lap"]["mean"], "+/-", agg["gamma_lap"]["std"],
              "gamma_tr", agg["gamma_tr"]["mean"], "+/-", agg["gamma_tr"]["std"],
              "acc", agg["accept"]["mean"])

if __name__ == "__main__":
    main()
