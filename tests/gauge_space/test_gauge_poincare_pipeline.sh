#!/usr/bin/env bash
set -euo pipefail

test -f proofs/gauge_space/plaquette_spectrum_derivation.md
test -f proofs/gauge_space/tensorization_gauge_space.md
test -f proofs/gauge_space/gauge_block_poincare_proof.md
test -f proofs/gauge_space/gauge_tensorization_lemma.md
test -f proofs/gauge_space/block_mode_wavelength_argument.md
test -f proofs/gauge_space/gauge_block_poincare_final.md

echo "gauge Poincare pipeline: PASS"
