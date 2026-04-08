from proofs.RPD.executable.rpd_6_two_bubble_incompatibility_check import (
    TwoBubbleIncompatibilityInput,
    check_two_bubble_incompatibility,
)


def test_two_bubble_incompatibility_positive_case() -> None:
    out = check_two_bubble_incompatibility(
        TwoBubbleIncompatibilityInput(bubble_a_present=True, bubble_b_present=False)
    )
    assert out.closes is True


def test_two_bubble_incompatibility_negative_case() -> None:
    out = check_two_bubble_incompatibility(
        TwoBubbleIncompatibilityInput(bubble_a_present=True, bubble_b_present=True)
    )
    assert out.closes is False
