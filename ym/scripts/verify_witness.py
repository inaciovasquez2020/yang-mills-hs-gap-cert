import json, sys
from jsonschema import Draft202012Validator

def main(path: str) -> int:
    schema_path = "witness/WITNESS.schema.json"
    with open(schema_path, "r", encoding="utf-8") as f:
        schema = json.load(f)
    with open(path, "r", encoding="utf-8") as f:
        obj = json.load(f)

    v = Draft202012Validator(schema)
    errs = sorted(v.iter_errors(obj), key=lambda e: e.path)

    if errs:
        for e in errs:
            loc = ".".join([str(x) for x in e.path]) if e.path else "<root>"
            print(f"FAIL {loc}: {e.message}")
        return 1

    print("OK: witness matches schema")
    print(f"kind = {obj.get('kind')}")
    return 0

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: python3 scripts/verify_witness.py witness/WITNESS.json")
        raise SystemExit(2)
    raise SystemExit(main(sys.argv[1]))
