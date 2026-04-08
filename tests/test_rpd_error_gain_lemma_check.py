from proofs.RPD.executable.rpd_error_gain_lemma_check import (
    ErrorGainLemmaInput,
    check_error_gain_lemma,
)


def test_error_gain_lemma_positive_case() -> None:
    out = check_error_gain_lemma(
        ErrorGainLemmaInput(e_main=3.0, e_gain=2.0, eta=1.0 / 3.0)
    )
    assert out.closes is True
    assert abs(out.gap - 1.0) < 1e-12


def test_error_gain_lemma_negative_case() -> None:
    out = check_error_gain_lemma(
        ErrorGainLemmaInput(e_main=3.0, e_gain=2.5, eta=1.0 / 3.0)
    )
    assert out.closes is False
