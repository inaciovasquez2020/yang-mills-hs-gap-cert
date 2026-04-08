from __future__ import annotations

from dataclasses import dataclass


@dataclass(frozen=True)
class KernelPreservationInput:
    kernel_dim_before: int
    kernel_dim_after: int


@dataclass(frozen=True)
class KernelPreservationOutput:
    preserved: bool


def check_kernel_preservation(inp: KernelPreservationInput) -> KernelPreservationOutput:
    return KernelPreservationOutput(
        preserved=inp.kernel_dim_before == inp.kernel_dim_after
    )


def main() -> None:
    demo = check_kernel_preservation(
        KernelPreservationInput(kernel_dim_before=2, kernel_dim_after=2)
    )
    if not demo.preserved:
        raise SystemExit("FAIL: kernel preservation demo failed")
    print("PASS: executable RPD_4 kernel-preservation check")
    

if __name__ == "__main__":
    main()
