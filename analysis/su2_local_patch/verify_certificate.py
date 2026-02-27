import json
import numpy as np
from fit_C1C2_weighted import build_forms, min_C1_for_C2

with open("su2_patch_certificate.json","r") as f:
    cert = json.load(f)

C1 = float(cert["C1_frozen"])
C2 = float(cert["C2_frozen"])

def check_one(n, k, seed):
    Aform, Bform, P0 = build_forms(n=n, k=k, seed=seed)
    need = min_C1_for_C2(Aform, Bform, P0, C2)
    return need <= C1 + 1e-9, need

fail = []
for k in cert["k_values_tested"]:
    for n in [200,320,400,520,700,900,1200]:
        for seed in range(cert["seed_range"][0], cert["seed_range"][1]+1):
            ok, need = check_one(n, k, seed)
            if not ok:
                fail.append((n,k,seed,need))

if fail:
    fail.sort(key=lambda t: t[3], reverse=True)
    print("FAIL", len(fail), "worst:", fail[0])
    raise SystemExit(1)

print("PASS: all tested (n,k,seed) satisfy need<=C1 with C1=",C1,"C2=",C2)
