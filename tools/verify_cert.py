import json, sys

with open(sys.argv[1]) as f:
    cert = json.load(f)

required = ["theorem_id","git_commit","status_hash","claims_hash","tests_passed"]

for r in required:
    if r not in cert:
        print("Certificate missing:", r)
        sys.exit(1)

if not cert["tests_passed"]:
    print("Tests not passed.")
    sys.exit(1)

print("Certificate verified.")
