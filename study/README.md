# Certificate study (2026-10-03)

Measured study behind the paper section "A measured certificate study on the deployed
gadget" (tab:certstudy): query-aware gnark v0.14.0 ScalarMul export (declared result
coordinates as targets), 20-variant hint-override sweep, complete affine-line search
(kernel dim <= 2), slice re-solve vs budgeted full-system solve ablation, and forged-hint
non-uniqueness pairs.

- exporter/: Go program (gnark v0.14.0) that regenerates every export deterministically.
  The 57 MB of witness/circuit JSON exports are NOT committed; run the exporter to
  recreate them (results/export-canonical-sha256.json pins their canonical digests, i.e. SHA-256 with the volatile timing/toolchain fields removed; python3 verify_exports.py checks a regeneration).
- results/: all measured outputs (timings are medians of 5 reps; environment pinned inside).
- certificate_checker.py: standalone stdlib reference checker (exhaustive F_3 self-check,
  720 projected-dimension cases, full F_257 line checks on the synthetic gadget).
- Every line certificate and forged pair was independently re-verified by direct
  substitution against all constraints before integration into the paper.
