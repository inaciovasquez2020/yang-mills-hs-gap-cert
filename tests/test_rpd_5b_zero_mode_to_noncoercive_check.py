from proofs.RPD.executable.rpd_5b_zero_mode_to_noncoercive_check import (
    ZeroModeToNoncoerciveInput,
    check_zero_mode_to_noncoercive,
)


def test_zero_mode_to_noncoercive_positive_case() -> None:
    out = check_zero_mode_to_noncoercive(
        ZeroModeToNoncoerciveInput(zero_mode_present=True, coercive_constant=0.0)
    )
    assert out.closes is True


def test_zero_mode_to_noncoercive_negative_case() -> None:
    out = check_zero_mode_to_noncoercive(
        ZeroModeToNoncoerciveInput(zero_mode_present=True, coercive_constant=1.0e-3)
    )
    assert out.closes is False
