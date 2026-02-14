import json, hashlib, sys
from numeric.hs_lattice_sum import hs_sum_eta, hs_sum_delta
from numeric.hs_tail_bound import tail_eta, tail_delta

def sha256(p):
    h = hashlib.sha256()
    with open(p,"rb") as f:
        h.update(f.read())
    return h.hexdigest()

cert_path = sys.argv[1]
cert = json.load(open(cert_path))

L = float(cert["params"]["L"])
Lambda = float(cert["params"]["Lambda"])
m0 = float(cert["params"]["m0"])

P = cert["params"].get("P", None)

if P is None:
    eta = float(cert["results"]["eta"])
    delta = float(cert["results"]["delta"])
else:
    P = int(P)
    eta = hs_sum_eta(L, Lambda, m0, P) + tail_eta(L, Lambda, m0, P)
    delta = hs_sum_delta(L, Lambda, m0, P) + tail_delta(L, Lambda, m0, P)
    cert["results"]["eta"] = round(eta, 6)
    cert["results"]["delta"] = round(delta, 6)

cert["results"]["pass"] = (eta + delta) < 1.0
cert["hashes"]["kernel_sha256"] = sha256(cert["inputs"]["kernel"])
cert["hashes"]["projector_sha256"] = sha256(cert["inputs"]["projector"])

json.dump(cert, open(cert_path,"w"), indent=2)
