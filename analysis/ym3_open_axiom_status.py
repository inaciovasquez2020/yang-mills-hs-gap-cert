from __future__ import annotations

from pathlib import Path
import re


YM3 = Path("YMFormal/YM3PhysicalReconstruction.lean")


def extract_axiom_names(text: str) -> list[str]:
    names: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^\s*axiom\s+([A-Za-z0-9_']+)", line)
        if m:
            names.append(m.group(1))
    return names


def main() -> None:
    text = YM3.read_text()
    axioms = extract_axiom_names(text)

    foundational = {
        "Scalar",
        "ZeroS",
        "OneS",
        "AddS",
        "MulS",
        "LeS",
        "LtS",
        "P",
        "Connection",
        "Measure",
        "IsReflectionPositive",
        "PhysicalHilbertSpace",
        "SelfAdjointOperator",
        "SpectralLowerBound",
        "TestFunction",
    }

    scaffold_open = {
        "reflection_reconstruction",
        "OsterwalderSchraderAxioms",
        "ReflectionPositivity",
        "GNSInnerProduct",
        "GNSSetoid",
        "GNSInnerProduct_compat",
        "GNSInner_pos",
        "GNSNull",
        "GNSNull_def",
        "GNSVacuumFn",
        "GNSHamiltonian",
        "GNSSpecGap",
    }

    allowed = foundational | scaffold_open
    unexpected = sorted(set(axioms) - allowed)
    missing = sorted(scaffold_open - set(axioms))

    print("YM3 axioms:", ", ".join(axioms))
    print("Unexpected axioms:", unexpected)
    print("Missing scaffold-open axioms:", missing)

    if unexpected:
        raise SystemExit(f"Unexpected YM3 axioms found: {unexpected}")
    if missing:
        raise SystemExit(f"Expected scaffold-open axioms missing: {missing}")


if __name__ == "__main__":
    main()
