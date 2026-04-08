from proofs.RPD.executable.rpd_5a_pulse_to_lambdamin_zero_check import (
    PulseToLambdaMinZeroInput,
    check_pulse_to_lambdamin_zero,
)


def test_pulse_to_lambdamin_zero_positive_case() -> None:
    out = check_pulse_to_lambdamin_zero(
        PulseToLambdaMinZeroInput(pulse_detected=True, lambda_min=0.0)
    )
    assert out.closes is True


def test_pulse_to_lambdamin_zero_negative_case() -> None:
    out = check_pulse_to_lambdamin_zero(
        PulseToLambdaMinZeroInput(pulse_detected=True, lambda_min=1.0e-3)
    )
    assert out.closes is False
