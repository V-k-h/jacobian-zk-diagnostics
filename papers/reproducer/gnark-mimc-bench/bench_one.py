#!/usr/bin/env python3
"""Time the augmented-Jacobian diagnostic on one exported gnark instance.

Reproduces one row of the paper's scale table (Table: public MiMCChain family).

Usage: bench_one.py <r1cs.json> <wit.json> [dense]
Prints one JSON line: sizes, Jacobian nnz, phase timings, peak RSS, verdict.
"""
import json
import os
import resource
import sys
import time

# compose/ lives three levels up from this reproducer directory
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                "..", "..", "..", "compose"))
import gnark_jacobian as gj


def main():
    r1cs_path, wit_path = sys.argv[1], sys.argv[2]
    backend = "pure" if len(sys.argv) > 3 and sys.argv[3] == "dense" else "sparse"

    t0 = time.perf_counter()
    d, p, cons = gj._load_r1cs(r1cs_path)
    wv = gj._load_witness(wit_path)
    t_load = time.perf_counter() - t0

    nwires = d["n_wires"]
    nfix = d["n_public"] + d["n_secret"]
    witness = {i: wv[i] for i in range(nwires)}
    fixed = set(range(nfix))

    # verify the witness satisfies every constraint before analysing
    t0 = time.perf_counter()
    for L, R, O in cons:
        lv = sum(c * witness[w] for w, c in L.items()) % p
        rv = sum(c * witness[w] for w, c in R.items()) % p
        ov = sum(c * witness[w] for w, c in O.items()) % p
        assert (lv * rv - ov) % p == 0
    t_verify = time.perf_counter() - t0

    t0 = time.perf_counter()
    rows = gj._jacobian_rows(cons, witness, fixed, p)
    t_rows = time.perf_counter() - t0
    nnz = sum(len(r) for r in rows)

    t0 = time.perf_counter()
    undet = gj.undetermined_wires(cons, witness, fixed, p, nwires, backend=backend)
    t_rank = time.perf_counter() - t0

    # ru_maxrss is bytes on macOS, kilobytes on Linux
    ru = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    rss_mib = ru / (1 << 20) if sys.platform == "darwin" else ru / (1 << 10)
    print(json.dumps({
        "backend": backend,
        "constraints": len(cons),
        "wires": nwires,
        "jacobian_nnz": nnz,
        "t_load_s": round(t_load, 3),
        "t_verify_s": round(t_verify, 3),
        "t_rows_s": round(t_rows, 3),
        "t_rank_s": round(t_rank, 3),
        "peak_rss_mib": round(rss_mib, 1),
        "n_undetermined": len(undet),
    }))


if __name__ == "__main__":
    main()
