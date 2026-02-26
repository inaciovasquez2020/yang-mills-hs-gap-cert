import json, pathlib

out = pathlib.Path("stress")
base = {
  "meta": {
    "toolkit_version": "urf/1.0",
    "cert_version": "ym-hs-gap/stress"
  },
  "inputs": {
    "kernel": "data/kernel_Rhat.bin",
    "projector": "data/projector_PiT.bin"
  },
  "hashes": {
    "kernel_sha256": "",
    "projector_sha256": ""
  }
}

Ls = [12, 16, 24, 32, 40]
Lambdas = [48, 64, 96, 128, 160]

for i,(L,La) in enumerate(zip(Ls,Lambdas), start=1):
    cert = dict(base)
    cert["params"] = {"L": float(L), "Lambda": float(La), "m0": 0.20}
    eta = 0.55 * (16/L)
    delta = 0.18 * (64/La)
    cert["results"] = {
        "eta": round(eta,3),
        "delta": round(delta,3),
        "pass": False
    }
    p = out / f"YM_HS_GAP_STRESS_{i:03d}.json"
    json.dump(cert, open(p,"w"), indent=2)
