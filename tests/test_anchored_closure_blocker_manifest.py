import json
import re
from pathlib import Path

def test_anchored_closure_blocker_manifest_matches_lean():
    manifest = json.loads(Path("manifests/anchored_closure_blockers.json").read_text())
    lean_text = Path("YMFormal/AnchoredClosure.lean").read_text()

    assert manifest["status"] == "conditional"
    assert manifest["file"] == "YMFormal/AnchoredClosure.lean"
    assert len(manifest["blockers"]) == 2

    for item in manifest["blockers"]:
        name = item["name"]
        assert item["kind"] == "axiom"
        assert item["required_replacement"] == "theorem"
        assert Path(item["proof_shell"]).is_file()
        assert re.search(rf"\baxiom\s+{re.escape(name)}\b", lean_text)
        assert not re.search(rf"\btheorem\s+{re.escape(name)}\b", lean_text)
