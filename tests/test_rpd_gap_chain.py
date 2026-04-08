from analysis.rpd_gap_chain import RPDGapInput, compute_rpd_gap_lower_bound


def test_rpd_gap_positive_case() -> None:
    out = compute_rpd_gap_lower_bound(
        RPDGapInput(beta=3.0, c_delta=1.0, C_local=0.5, C_gain=1.0)
    )
    assert out.C_prime == 1.0
    assert out.c_gap == 2.0
    assert out.closes is True


def test_rpd_gap_negative_case() -> None:
    out = compute_rpd_gap_lower_bound(
        RPDGapInput(beta=1.0, c_delta=1.0, C_local=0.75, C_gain=1.0)
    )
    assert out.C_prime == 1.5
    assert out.c_gap == -0.5
    assert out.closes is False
