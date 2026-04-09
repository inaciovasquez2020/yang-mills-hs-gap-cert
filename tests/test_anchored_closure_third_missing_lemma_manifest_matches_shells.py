import json
from pathlib import Path

def test_anchored_closure_third_missing_lemma_manifest_matches_shells():
    manifest = json.loads(
        Path("manifests/anchored_closure_third_missing_lemmas.json").read_text()
    )

    for item in manifest["blockers"]:
        shell_text = Path(item["proof_shell"]).read_text()
        assert item["third_missing_lemma"] in shell_text
