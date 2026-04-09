import json
from pathlib import Path

def test_anchored_closure_dependency_chains_match_shells():
    manifest = json.loads(
        Path("manifests/anchored_closure_dependency_chains.json").read_text()
    )

    for item in manifest["chains"]:
        shell_text = Path(item["proof_shell"]).read_text()
        for step in item["steps"]:
            assert step in shell_text
