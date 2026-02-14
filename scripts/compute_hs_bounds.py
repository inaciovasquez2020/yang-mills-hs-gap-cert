import json, hashlib, sys, os
from analytic.hs_upper_bound import hs_bound_eta, hs_bound_delta

def sha256(p):
    h = hashlib.sha256()
    with open(p,"rb") as f:
        h.update(f.read())
    return h.hexdigest()

cert_path = sys.argv[1]
cert = json.load(open(cert_path))

L = cert["params"]["L"]
Lambda = cert["params"]["Lambda"]

# analytic upper bounds
eta = hs_bound_eta(L, Lambda)
delta = hs_bound_delta(L, Lambda)

cert["results"]["eta"] = round(eta, 4)
cert["results"]["delta"] = round(delta, 4)
cert["results"]["pass"] = (eta + delta) < 1.0

cert["hashes"]["kernel_sha256"] = sha256(cert["inputs"]["kernel"])
cert["hashes"]["projector_sha256"] = sha256(cert["inputs"]["projector"])

json.dump(cert, open(cert_path,"w"), indent=2)

