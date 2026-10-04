# Jacobian Diagnostics for Under-Constrained Zero-Knowledge Circuits

Reproduction code for the paper (IACR ePrint 2026/1852). Every measured
table and claim in the paper regenerates from this repository alone; the
industrial corpus mentioned in the paper is not required and not included.

## Requirements

- Python 3.9+ (standard library only — every analysis engine is dependency-free)
- Go ≥ 1.24 (gnark v0.14.0 and v0.16.2 are fetched via the module system;
  each `go.sum` pins them)
- Lean 4 + Lake, optional, only for the kernel-checked certificates
  (`lean/lean-toolchain` pins the toolchain; mathlib v4.15.0 resolves via
  `lakefile.lean`)
- circom + Racket/cvc5, optional, only for the external corpus study
  (see `study/corpus_line_study.py --help`)

## One command

```bash
make check     # dependency-free self-tests and controls (Python only, ~minutes)
make tables    # every measured table of the evaluation (Go + Python)
make study     # deployed-gadget certificate study (regenerates exports first)
bash run_all.sh   # = check + tables + study
```

or, fully containerized:

```bash
docker build -t jacobian-diagnostics . && docker run --rm jacobian-diagnostics
```

Optional extras: `make advisory` (the vulnerable/patched gnark advisory pairs,
including Groth16 prove-level checks) and `make lean` (kernel-checked
certificates; the first build compiles mathlib and takes a while).

## What reproduces what

| Paper object | Command / driver |
|---|---|
| Table (scale): MiMCChain family, 990–66,000 constraints | `make tables` → `frontends/gnark` harness + `papers/reproducer/gnark-mimc-bench/bench_one.py` |
| Table (topo): Merkle-path / EdDSA / MiMC-tree | same driver, topology-diverse circuits |
| Table (locality): ScalarMul 20-variant adversarial sweep | `make tables` → `harness adversarial scalarmul` + `compose/gnark_jacobian.py` |
| Second-witness confirmation (5/5 flagged wires) | `make tables` → `papers/reproducer/gnark-scalarmul/second_witness_flagged.py` |
| PLONKish (SparseR1CS) end-to-end check | `make tables` → `harness plonk scalarmul` + unchanged diagnostic |
| Theorem D (witness-locality separation) + Theorem E certificates | `make check` → `papers/reproducer/toy_hint_gadget.py` |
| Taxonomy table (caught/missed classes) | `make check` → `papers/reproducer/taxonomy_runs.py` |
| Reference checker self-tests (exhaustive F_3, full F_257 lines) | `make check` → `study/certificate_checker.py` |
| Certificate study table (tab:certstudy): line certificates, slice re-solve vs. full-solve ablation, forged pairs | `make study` → `study/line_search.py`, `study/solve_ablation.py`, `study/run_measurements.py` |
| Parabola certificates (Theorem F) incl. curved-branch classification | `make study` → `study/parabola_certificate.py` |
| Gröbner elimination on the refused slices | `make study` → `study/groebner_slice.py` |
| Advisory pair, ScalarMul: v0.14.0 forgery accepted / v0.16.2 rejected at `groth16.Prove` | `make advisory` → `study/exporter-patched` (`prove`), `study/exporter-advisory` |
| Advisory pair, emulated ModMul: shifted-remainder forgery + diagnostic | `make advisory` → `study/exporter-patched` (`modmul`), `study/exporter-advisory` |
| Commitment-as-advice relaxation measurements | `make advisory` → `study/exporter-patched` (`advice`) + `study/analyze.py` |
| Corpus line-certificate coverage (78 circom/Picus circuits) | `study/corpus_line_study.py --circom <bin> --ronin <dir> --bench <dir>` (external deps; measured outputs committed under `study/results/`) |
| Kernel-checked certificates (redundancy differential step, affine-line and parabola expansions) | `make lean` → `lean/RedundancyCert.lean`, `lean/AffineLineCert.lean` |

Pre-exported instances for the two case studies (`circuit.r1cs.json`, honest and
degenerate witnesses) are committed under `papers/reproducer/gnark-scalarmul/`
and `papers/reproducer/gnark-plonk/`, so those rows reproduce without Go. The
~50 MB of certificate-study exports are not committed; `make study` regenerates
them and verifies them against `study/results/export-canonical-sha256.json`
(canonical SHA-256, with the volatile timing/toolchain fields removed).
All measured outputs behind the paper's numbers are committed under
`study/results/` for direct comparison.

## Layout

- `compose/gnark_jacobian.py` — the augmented-Jacobian diagnostic (exact sparse
  elimination over the circuit field); `gnark_sparse.py` is the elimination
  core; `r1cs_iden3.py` / `r1cs_to_iden3.py` convert between the JSON export
  format and iden3 binary `.r1cs`.
- `frontends/gnark/` — gnark v0.14.0 harness: circuit export, witness export,
  the adversarial hint-degeneracy sweep, and the PLONK (SparseR1CS) exporter.
  `thirdparty/dump.go` (build-ignored) exports any third-party gnark circuit
  into the same R1CS JSON.
- `papers/reproducer/` — per-table drivers and the dependency-free synthetic
  reproducer.
- `study/` — the measured certificate study: reference checker, complete
  affine-line search, parabola certificates, Gröbner slice elimination, solve
  ablation, corpus study, and the three Go exporters (`exporter/` v0.14.0
  query-aware ScalarMul, `exporter-patched/` v0.16.2 with prove/advice/modmul
  modes, `exporter-advisory/` v0.14.0 emulated ModMul with the shifted hint).
  `study/results/` holds every measured output cited in the paper.
- `lean/` — kernel-checked certificates: the determinacy certificate checker
  (`R1CSChecker.lean`), the local-redundancy differential step
  (`RedundancyCert.lean`), the affine-line/parabola expansions
  (`AffineLineCert.lean`), and generated demos. Check one in place with
  `cd lean && lake env lean GnarkFullDemo.lean`.

## Relation to the paper

Section numbers refer to the ePrint version. The scale and topology tables are
Section "Exact sparse linear algebra at circuit scale"; the adversarial sweep
and second-witness confirmation are Section "Witness locality"; the synthetic
reproducer and its Theorem E certificate checks are Sections "A synthetic
reproducer" and "From infinitesimal freedom to finite-field counterexamples";
the certificate study, advisory pairs, and commitment-as-advice measurements
are Section "A measured certificate study on the deployed gadget"; the corpus
coverage is Section "Line-certificate coverage on a public corpus"; the
taxonomy runs are Section "A public soundness benchmark and an applicability
taxonomy".

## License

MIT (see `LICENSE`).
