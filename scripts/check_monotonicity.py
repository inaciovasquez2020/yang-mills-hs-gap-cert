import json, sys, glob

paths = sorted(glob.glob("certs/YM_HS_GAP_CERT_*.json"))
etas = []
deltas = []

for p in paths:
    j = json.load(open(p))
    etas.append(j["results"]["eta"])
    deltas.append(j["results"]["delta"])

for i in range(1, len(etas)):
    assert etas[i] <= etas[i-1], f"eta not monotone at index {i}"
    assert deltas[i] <= deltas[i-1], f"delta not monotone at index {i}"

print("PASS: monotonicity across certificates")
