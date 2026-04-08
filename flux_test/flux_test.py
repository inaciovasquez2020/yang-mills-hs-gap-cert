import argparse, math
import pandas as pd

def wilson(p, n, z=1.96):
    if n == 0:
        return (float("nan"), float("nan"))
    denom = 1 + z*z/n
    center = (p + z*z/(2*n)) / denom
    half = (z * math.sqrt((p*(1-p) + z*z/(4*n))/n)) / denom
    return (max(0.0, center - half), min(1.0, center + half))

ap = argparse.ArgumentParser()
ap.add_argument("--csv", required=True)
ap.add_argument("--qcol", default="Q")
ap.add_argument("--tcol", default="T")
ap.add_argument("--group", default="n")
if __name__ == '__main__':
    args = ap.parse_args()

df = pd.read_csv(args.csv)
rows = []
for n, g in df.groupby(args.group):
    Q = g[args.qcol].to_numpy()
    T = g[args.tcol].to_numpy()
    nobs = len(Q)
    phat = float((Q > T).mean())
    lo, hi = wilson(phat, nobs)
    rows.append((n, nobs, phat, lo, hi))
out = pd.DataFrame(rows, columns=[args.group, "samples", "p_hat", "ci_lo", "ci_hi"]).sort_values(args.group)
print(out.to_string(index=False))
print("global_p_hat", float((df[args.qcol].to_numpy() > df[args.tcol].to_numpy()).mean()))
