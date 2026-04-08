from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class PulseToLambdaMinZeroInput:
    pulse_detected: bool
    lambda_min: float
    tol: float = 1e-12


@dataclass(frozen=True)
class PulseToLambdaMinZeroOutput:
    closes: bool


def check_pulse_to_lambdamin_zero(
    inp: PulseToLambdaMinZeroInput,
) -> PulseToLambdaMinZeroOutput:
    closes = (not inp.pulse_detected) or (abs(inp.lambda_min) <= inp.tol)
    return PulseToLambdaMinZeroOutput(closes=closes)


def main() -> None:
    demo = check_pulse_to_lambdamin_zero(
        PulseToLambdaMinZeroInput(pulse_detected=True, lambda_min=0.0)
    )
    if not demo.closes:
        raise SystemExit("FAIL: pulse-to-lambda_min-zero demo failed")
    print("PASS: executable RPD_5A pulse-to-lambda_min-zero check")


if __name__ == "__main__":
    main()
