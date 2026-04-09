from analysis.ym3_open_axiom_status import extract_axiom_names
from pathlib import Path


def test_ym3_open_axiom_status_is_stable() -> None:
    text = Path("YMFormal/YM3PhysicalReconstruction.lean").read_text()
    axioms = set(extract_axiom_names(text))

    assert "GNSSpecGap" in axioms
    for still_open in [
        "reflection_reconstruction",
        "GNSInnerProduct",
        "GNSSetoid",
        "GNSInnerProduct_compat",
        "GNSInner_pos",
        "GNSNull",
        "GNSNull_def",
        "OsterwalderSchraderAxioms",
        "ReflectionPositivity",
        "GNSVacuumFn",
        "GNSHamiltonian",
        "GNSSpecGap",
    ]:
        assert still_open in axioms

    assert "GNSNull" in axioms
    assert "GNSNull_def" in axioms

    for eliminated in [
        "GNSQuotient",
        "GNSProj",
        "GNSEquiv",
        "GNSInner",
        "GNSVacuum",
        "GNSHilbert",
        "GNSProj_respects_GNSEquiv",
        "GNSInner_respects_GNSEquiv",
    ]:
        assert eliminated not in axioms
