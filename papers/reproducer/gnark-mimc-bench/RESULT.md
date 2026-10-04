# Public scale benchmark (MiMCChain family)

Circuit: `frontends/gnark/bench_public.go` `MiMCChain` — N chained MiMC permutations of a
single public input X on BN254 (gnark v0.14.0, 330 constraints per permutation), final digest
deliberately unpinned so the solver fills every internal round wire from X alone. Ground truth:
**all internal wires DETERMINED**. Uses only gnark's standard library — no client code — so the
circuit, the exported instances, and this driver are all publishable.

Pipeline (from `zk-soundness-monitor/`):

    cd frontends/gnark && GOWORK=off go build -o /tmp/zksm-gnark .
    for n in 3 20 60 120 200; do
      GNARK_MIMC=$n /tmp/zksm-gnark mimcchain      /tmp/bench-c$n.r1cs.json
      GNARK_MIMC=$n /tmp/zksm-gnark witness mimcchain /tmp/bench-c$n.wit.json
    done
    python3 papers/reproducer/gnark-mimc-bench/bench_one.py /tmp/bench-c$n.r1cs.json /tmp/bench-c$n.wit.json [dense]

Each row = one process (clean per-instance peak RSS). "rank" = the sparse elimination call;
"total" = load + full witness verification + Jacobian assembly + rank.

## Sparse backend (the paper's Table, measured 2026-09-10)

| N   | constraints | wires  | Jac nnz | rank (s) | total (s) | peak RSS (MiB) | verdict |
|-----|-------------|--------|---------|----------|-----------|----------------|---------|
| 3   | 990         | 992    | 2,978   | 0.007    | 0.012     | 16             | all determined |
| 20  | 6,600       | 6,602  | 20,182  | 0.038    | 0.069     | 41             | all determined |
| 60  | 19,800      | 19,802 | 62,942  | 0.121    | 0.216     | 105            | all determined |
| 120 | 39,600      | 39,602 | 133,082 | 0.308    | 0.512     | 211            | all determined |
| 200 | 66,000      | 66,002 | 237,802 | 0.564    | 0.985     | 360            | all determined |

## Dense baseline (pure-Python elimination, same machine)

| N | constraints | rank (s) | peak RSS (MiB) |
|---|-------------|----------|----------------|
| 1 | 330         | 0.681    | 18             |
| 3 | 990         | 16.882   | 112            |

At 990 constraints the dense baseline is already ~2,400× slower than sparse (16.9 s vs 7 ms) and
grows cubically; it completes at none of the larger sizes.

Also measured in the same harness: the gnark-scalarmul case-study R1CS (2,396 constraints,
honest witness) — rank 0.014 s, total 0.024 s, 22 MiB, all determined.

Machine: Apple M4 Pro (14 cores, 48 GiB), macOS 15.1, CPython 3.14.7, Go 1.25.12, gnark v0.14.0.

Near-linear scaling here reflects the low fill-in of this chain-structured Jacobian under
Markowitz pivoting; fill-in is circuit-dependent, so this is an observation about the family,
not a general guarantee (the paper says exactly this).

## Topology-diverse public instances (paper Table: topo, same machine/harness)

| Instance                      | circuit name / env        | constraints | Jac nnz | rank (s) | total (s) | RSS (MiB) | verdict |
|-------------------------------|---------------------------|-------------|---------|----------|-----------|-----------|---------|
| Merkle path depth 5 (MiMC)    | merklepath GNARK_MERKLE_K=5  | 3,647    | 26,497  | 0.084    | 0.114     | 43        | all determined |
| EdDSA verify                  | eddsaverify               | 7,675       | 28,913  | 0.096    | 0.134     | 50        | all determined |
| Merkle path depth 20 (MiMC)   | merklepath GNARK_MERKLE_K=20 | 13,592   | 269,459 | 0.699    | 0.964     | 307       | all determined |
| MiMC tree, 64 leaves          | mimctree GNARK_TREE_K=6   | 41,580      | 239,213 | 0.549    | 0.864     | 311       | all determined |

Note the depth-20 Merkle path: more Jacobian nnz and slower rank than the 3x-larger MiMC tree —
elimination cost tracks structure/fill-in, not constraint count.

SHA-256 (gnark std sha2, 183,144 constraints) compiles but its witness cannot be solved outside a
proving backend: gnark's uints range tables use the commitment API ("placeholder function: to be
replaced by commitment computation"). Commitment-using circuits need witness export via a full
prover run — out of scope for this harness today.
