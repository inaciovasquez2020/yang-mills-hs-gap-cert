import json, hashlib, sys

def sha256(p):
    h = hashlib.sha256()
    with open(p,"rb") as f:
        h.update(f.read())
    return h.hexdigest()

cert_path = sys.argv[1]
cert = json.load(open(cert_path))

cert["hashes"]["kernel_sha256"] = sha256(cert["inputs"]["kernel"])
cert["hashes"]["projector_sha256"] = sha256(cert["inputs"]["projector"])
cert["results"]["pass"] = (
    cert["results"]["eta"] + cert["results"]["delta"] < 1.0
)

json.dump(cert, open(cert_path,"w"), indent=2)
