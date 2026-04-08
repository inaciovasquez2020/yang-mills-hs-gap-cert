from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class RPDGapInput:
    beta: float
    c_delta: float
    C_local: float
    C_gain: float


@dataclass(frozen=True)
class RPDGapOutput:
    C_prime: float
    c_gap: float
    closes: bool


def compute_rpd_gap_lower_bound(inp: RPDGapInput) -> RPDGapOutput:
    """
    Symbolic numeric gate for the inequality
        gamma_B >= (beta * c_delta - C') * L^{-2},
    where
        C' = C_local * (1 + C_gain).
    This does not prove the theorem.
    It only evaluates the positivity condition for supplied constants.
    """
    C_prime = inp.C_local * (1.0 + inp.C_gain)
    c_gap = inp.beta * inp.c_delta - C_prime
    return RPDGapOutput(C_prime=C_prime, c_gap=c_gap, closes=(c_gap > 0.0))


if __name__ == "__main__":
    sample = RPDGapInput(beta=2.0, c_delta=1.0, C_local=0.25, C_gain=0.5)
    out = compute_rpd_gap_lower_bound(sample)
    print(
        {
            "C_prime": out.C_prime,
            "c_gap": out.c_gap,
            "closes": out.closes,
        }
    )
