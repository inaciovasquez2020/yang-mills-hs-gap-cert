from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class ZeroModeToNoncoerciveInput:
    zero_mode_present: bool
    coercive_constant: float
    tol: float = 1e-12


@dataclass(frozen=True)
class ZeroModeToNoncoerciveOutput:
    closes: bool


def check_zero_mode_to_noncoercive(
    inp: ZeroModeToNoncoerciveInput,
) -> ZeroModeToNoncoerciveOutput:
    closes = (not inp.zero_mode_present) or (inp.coercive_constant <= inp.tol)
    return ZeroModeToNoncoerciveOutput(closes=closes)


def main() -> None:
    demo = check_zero_mode_to_noncoercive(
        ZeroModeToNoncoerciveInput(zero_mode_present=True, coercive_constant=0.0)
    )
    if not demo.closes:
        raise SystemExit("FAIL: zero-mode-to-noncoercive demo failed")
    print("PASS: executable RPD_5B zero-mode-to-noncoercive check")


if __name__ == "__main__":
    main()
