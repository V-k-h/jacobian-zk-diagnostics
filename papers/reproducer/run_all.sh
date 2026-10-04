#!/usr/bin/env bash
# Reproduce every measured table in the paper from public source, end to end.
#
#   bash papers/reproducer/run_all.sh
#
# Requires: Go (module cache or network for gnark v0.14.0), Python 3. Run from
# anywhere; paths are resolved relative to this script. Regenerates:
#   - Table (scale):    the MiMCChain family, 990..66,000 constraints
#   - Table (topo):     Merkle-path / EdDSA / MiMC-tree instances
#   - Table (locality): the ScalarMul 20-variant adversarial sweep
#   - the second-witness confirmation on the degenerate branch
#   - the PLONKish (SparseR1CS) end-to-end check
#   - the synthetic 20-constraint reproducer and the taxonomy runs
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
OUT="${TMPDIR:-/tmp}/zksm-repro"
BIN="$OUT/zksm-gnark"
mkdir -p "$OUT"

echo "== build harness (gnark v0.14.0)"
(cd "$ROOT/frontends/gnark" && GOWORK=off go build -o "$BIN" .)

echo
echo "== Table (scale): MiMCChain family"
for n in 3 20 60 120 200; do
  GNARK_MIMC=$n "$BIN" mimcchain "$OUT/chain$n.r1cs.json" 2>/dev/null
  GNARK_MIMC=$n "$BIN" witness mimcchain "$OUT/chain$n.wit.json" 2>/dev/null
  python3 "$HERE/gnark-mimc-bench/bench_one.py" "$OUT/chain$n.r1cs.json" "$OUT/chain$n.wit.json"
done

echo
echo "== Table (topo): topology-diverse instances"
GNARK_MERKLE_K=5  "$BIN" merklepath "$OUT/merkle5.r1cs.json"  2>/dev/null
GNARK_MERKLE_K=5  "$BIN" witness merklepath "$OUT/merkle5.wit.json"  2>/dev/null
GNARK_MERKLE_K=20 "$BIN" merklepath "$OUT/merkle20.r1cs.json" 2>/dev/null
GNARK_MERKLE_K=20 "$BIN" witness merklepath "$OUT/merkle20.wit.json" 2>/dev/null
"$BIN" eddsaverify "$OUT/eddsa.r1cs.json" 2>/dev/null
"$BIN" witness eddsaverify "$OUT/eddsa.wit.json" 2>/dev/null
GNARK_TREE_K=6 "$BIN" mimctree "$OUT/tree6.r1cs.json" 2>/dev/null
GNARK_TREE_K=6 "$BIN" witness mimctree "$OUT/tree6.wit.json" 2>/dev/null
for f in merkle5 eddsa merkle20 tree6; do
  python3 "$HERE/gnark-mimc-bench/bench_one.py" "$OUT/$f.r1cs.json" "$OUT/$f.wit.json"
done

echo
echo "== Table (locality): ScalarMul adversarial sweep (gnark 0.14.0, BN254)"
"$BIN" adversarial scalarmul "$OUT/sm" 2>/dev/null | tail -1 || true
for wf in "$OUT"/sm/wit.*.json; do
  echo "-- $(basename "$wf")"
  python3 "$ROOT/compose/gnark_jacobian.py" "$OUT/sm/circuit.r1cs.json" "$wf" inputs | tail -1
done

echo
echo "== second-witness confirmation on the degenerate branch"
python3 "$HERE/gnark-scalarmul/second_witness_flagged.py" \
  "$OUT/sm/circuit.r1cs.json" "$OUT/sm/wit.h726531982-zero.json" 261 262 264 265 266

echo
echo "== PLONKish (SparseR1CS) end-to-end check"
"$BIN" plonk scalarmul "$OUT/plonk" 2>/dev/null | tail -1 || true
for wf in "$OUT"/plonk/wit.*.json; do
  echo "-- $(basename "$wf")"
  python3 "$ROOT/compose/gnark_jacobian.py" "$OUT/plonk/circuit.r1cs.json" "$wf" inputs | tail -1
done

echo
echo "== synthetic 20-constraint reproducer + taxonomy runs"
python3 "$HERE/toy_hint_gadget.py"
python3 "$HERE/taxonomy_runs.py"

echo
echo "all reproductions complete; outputs under $OUT"
