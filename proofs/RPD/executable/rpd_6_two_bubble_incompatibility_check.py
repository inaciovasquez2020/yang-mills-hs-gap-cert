from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class TwoBubbleIncompatibilityInput:
    bubble_a_present: bool
    bubble_b_present: bool


@dataclass(frozen=True)
class TwoBubbleIncompatibilityOutput:
    closes: bool


def check_two_bubble_incompatibility(
    inp: TwoBubbleIncompatibilityInput,
) -> TwoBubbleIncompatibilityOutput:
    closes = not (inp.bubble_a_present and inp.bubble_b_present)
    return TwoBubbleIncompatibilityOutput(closes=closes)


def main() -> None:
    demo = check_two_bubble_incompatibility(
        TwoBubbleIncompatibilityInput(bubble_a_present=True, bubble_b_present=False)
    )
    if not demo.closes:
        raise SystemExit("FAIL: two-bubble-incompatibility demo failed")
    print("PASS: executable RPD_6 two-bubble-incompatibility check")


if __name__ == "__main__":
    main()
