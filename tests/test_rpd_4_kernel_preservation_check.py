from proofs.RPD.executable.rpd_4_kernel_preservation_check import (
    KernelPreservationInput,
    check_kernel_preservation,
)


def test_kernel_preservation_positive_case() -> None:
    out = check_kernel_preservation(
        KernelPreservationInput(kernel_dim_before=3, kernel_dim_after=3)
    )
    assert out.preserved is True


def test_kernel_preservation_negative_case() -> None:
    out = check_kernel_preservation(
        KernelPreservationInput(kernel_dim_before=3, kernel_dim_after=2)
    )
    assert out.preserved is False
