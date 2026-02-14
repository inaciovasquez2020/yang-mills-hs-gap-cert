Examples and Counterexamples

Passing Example
examples/YM_HS_GAP_EXAMPLE_PASS.json
Demonstrates eta + delta < 1 at larger (L, Λ), validating the HS-gap criterion.

Failing Counterexample
counterexamples/YM_HS_GAP_COUNTEREXAMPLE_FAIL.json
Violates eta + delta < 1 by construction.
Included to show necessity of the inequality and guard against false positives.

Policy
CI enforces only certified YM_HS_GAP_CERT_*.json.
Examples and counterexamples are excluded from CI pass/fail gating by design.

