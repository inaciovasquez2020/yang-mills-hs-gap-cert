from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ErrorGainLemmaInput:
    e_main: float
    e_gain: float
    eta: float


@dataclass(frozen=True)
class ErrorGainLemmaOutput:
    closes: bool
    gap: float


def check_error_gain_lemma(inp: ErrorGainLemmaInput) -> ErrorGainLemmaOutput:
    closes = (
        inp.eta > 0.0
        and inp.e_main > 0.0
        and inp.e_gain <= (1.0 - inp.eta) * inp.e_main
    )
    gap = inp.e_main - inp.e_gain
    return ErrorGainLemmaOutput(closes=closes, gap=gap)


def main() -> None:
    demo = check_error_gain_lemma(
        ErrorGainLemmaInput(e_main=3.0, e_gain=2.0, eta=1.0 / 3.0)
    )
    if not demo.closes:
        raise SystemExit("FAIL: conditional RPD_ERROR_GAIN_LEMMA check failed")
    print("PASS: conditional executable RPD_ERROR_GAIN_LEMMA check")


if __name__ == "__main__":
    main()
