#!/usr/bin/env python3
"""Projected target dimension on the PLONKish (SparseR1CS) export.

Runs the diagnostic of analyze.py on the committed PLONK export of the paper's
case study (papers/reproducer/gnark-plonk/), with the paper's query F = {one,
declared input}, at the honest and degenerate witnesses, and reports rank,
nullity, the moving-wire count, and r_T over the moving wires. Writes
results/plonk-rT.json.
"""
import json
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze import jacobian, echelon, affine
from certificate_checker import rank as dense_rank

ROOT = Path(__file__).resolve().parent
PLONK = ROOT / ".." / "reproducer" / "gnark-plonk"


def load_monitor(path):
    d = json.loads(Path(path).read_text())
    p = int(d["prime"])

    def side(terms):
        const, coeff = 0, {}
        for c, w in terms:
            c, w = int(c) % p, int(w)
            if w == 0:
                const = (const + c) % p
            else:
                coeff[w] = (coeff.get(w, 0) + c) % p
        return (const, {j: c for j, c in coeff.items() if c})

    rows = [(side(c["L"]), side(c["R"]), side(c["O"])) for c in d["constraints"]]
    return d, p, rows


def main():
    d, p, rows = load_monitor(PLONK / "circuit.r1cs.json")
    n = d["n_wires"]
    fixed = [0, 1]  # synthetic ONE + the one declared input (paper's query)
    out = []
    for witname, label in (("wit.honest.json", "honest"), ("wit.degenerate.json", "degenerate")):
        w = json.loads((PLONK / witname).read_text())
        a = [int(x) % p for x in (w.get("witness") or w.get("values") or w)]
        bad = [i for i, (l, r, o) in enumerate(rows)
               if (affine(l, a, p) * affine(r, a, p) - affine(o, a, p)) % p]
        assert not bad, f"witness fails rows {bad[:5]}"
        t0 = time.perf_counter()
        M = [{j: 1} for j in fixed] + jacobian(rows, a, p)
        pivots, free, expr, stats = echelon(M, n, p)
        nullity = len(free)
        moving = sorted(j for j in range(n) if expr[j])
        target_rows = [[expr[j].get(k, 0) for k in free] for j in moving]
        r_t = dense_rank(target_rows, p) if target_rows else 0
        rec = {"witness": label, "constraints": len(rows), "wires": n,
               "fixed": fixed, "rank": n - nullity, "nullity": nullity,
               "moving_wires": len(moving), "projected_target_dimension": r_t,
               "seconds": round(time.perf_counter() - t0, 4)}
        out.append(rec)
        print(rec)
    (ROOT / "results" / "plonk-rT.json").write_text(json.dumps(out, indent=1) + "\n")


if __name__ == "__main__":
    main()
