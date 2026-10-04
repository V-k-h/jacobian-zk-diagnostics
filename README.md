# Artifact: Jacobian Diagnostics for Under-Constrained Zero-Knowledge Circuits

Reproduction artifact for the paper (IACR ePrint 2026/1852). Every measured
table and claim in the paper regenerates from this repository alone; the
industrial corpus mentioned in the paper is not required and not included.

## Requirements

- Go ≥ 1.21 (gnark v0.14.0 is fetched via the module system; `go.sum` pins it)
- Python 3.9+ (standard library only — the engines are dependency-free)
- Lean 4 + Lake (optional, only for the kernel-checked certificates;
  `lean/lean-toolchain` pins the toolchain, mathlib resolves via `lakefile.lean`)

## One command

```bash
bash papers/reproducer/run_all.sh
```

regenerates, end to end (outputs under `$TMPDIR/zksm-repro`):

| Paper object | What runs |
|---|---|
| Table (scale): MiMCChain family, 990–66,000 constraints | `frontends/gnark` harness exports R1CS+witness; `papers/reproducer/gnark-mimc-bench/bench_one.py` times the diagnostic per instance |
| Table (topo): Merkle-path / EdDSA / MiMC-tree | same driver, topology-diverse circuits |
| Table (locality): ScalarMul 20-variant adversarial sweep | `harness adversarial scalarmul` + `compose/gnark_jacobian.py` per satisfiable witness |
| Second-witness confirmation (5/5 flagged wires) | `papers/reproducer/gnark-scalarmul/second_witness_flagged.py` |
| PLONKish (SparseR1CS) end-to-end check | `harness plonk scalarmul` + unchanged diagnostic |
| Theorem D (witness-locality separation) + Theorem E certificates | `papers/reproducer/toy_hint_gadget.py` — exact arithmetic, checks the 0→5 signature, the retained-row rank, the local-redundancy identities (Schwartz–Zippel), and the Lang–Weil budget |
| Taxonomy table (caught/missed classes) | `papers/reproducer/taxonomy_runs.py` |

Pre-exported instances for the two case studies (`circuit.r1cs.json`, honest and
degenerate witnesses) are committed under `papers/reproducer/gnark-scalarmul/`
and `papers/reproducer/gnark-plonk/`, so those rows reproduce without Go.

## Layout

- `compose/gnark_jacobian.py` — the augmented-Jacobian diagnostic (exact sparse
  elimination over the circuit field); `gnark_sparse.py` is the elimination core.
- `frontends/gnark/` — gnark v0.14.0 harness: circuit export, witness export,
  the adversarial hint-degeneracy sweep, and the PLONK (SparseR1CS) exporter.
  `thirdparty/dump.go` (build-ignored) exports any third-party gnark circuit
  into the same R1CS JSON.
- `papers/reproducer/` — per-table drivers and the dependency-free synthetic
  reproducer.
- `lean/` — the kernel-checked determinacy certificate checker
  (`R1CSChecker.lean`) and generated certificate demos; check one in place with
  `cd lean && lake env lean GnarkFullDemo.lean`.

## Relation to the paper

Section numbers refer to the ePrint version. The scale and topology tables are
Section "Exact sparse linear algebra at circuit scale"; the adversarial sweep
and second-witness confirmation are Section "Witness locality"; the synthetic
reproducer and its Theorem E certificate checks are Sections "A synthetic
reproducer" and "From infinitesimal freedom to finite-field counterexamples";
the taxonomy runs are Section "A public soundness benchmark and an
applicability taxonomy".

## License

MIT (see `LICENSE`).
