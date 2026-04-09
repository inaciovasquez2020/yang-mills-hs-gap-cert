import json
from pathlib import Path

def test_second_missing_lemmas_lean_shell_matches_manifest():
    manifest = json.loads(
        Path("manifests/anchored_closure_second_missing_lemmas.json").read_text()
    )
    lean_text = Path("YMFormal/AnchoredClosure/SecondMissingLemmas.lean").read_text()

    for item in manifest["blockers"]:
        assert f"axiom {item['second_missing_lemma']}" in lean_text
