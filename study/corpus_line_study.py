#!/usr/bin/env python3
"""Corpus-level line-certificate coverage on the Picus benchmark corpus.

Pipeline, per circom benchmark circuit (relative includes resolve in place):
  1. compile with circom --r1cs --O0 (the Picus evaluation's optimisation level);
  2. run ronin (the local Picus fork) on the .r1cs with a wall-clock budget,
     collecting the verdict and, when underconstrained, the counterexample pair;
  3. where a counterexample pair (a, b) exists: verify both witnesses against the
     R1CS, run the pointwise diagnostic at each (rank, nullity, r_T over the
     declared outputs), run the complete affine-line search when nullity <= 2,
     and test the Picus difference direction v = b - a itself: is it tangent at
     a, and does it satisfy the line certificate?

Usage:
  python3 corpus_line_study.py --circom <circom-binary> --ronin <ronin-dir> \
      --bench <benchmarks-dir> [--sets circomlib-cff5ab6,motivating] \
      [--budget 60] [--max-constraints 50000]

Writes results/corpus-line-study.json and prints a summary table. The ronin
checkout is read-only; everything is written under this study directory or /tmp.
"""
import argparse
import json
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
for _up in Path(__file__).resolve().parents:
    if (_up / "compose" / "r1cs_iden3.py").exists():
        sys.path.insert(0, str(_up / "compose"))
        break

import r1cs_iden3
from analyze import echelon, jacobian
from certificate_checker import rank as dense_rank
from line_search import search as line_search

ROOT = Path(__file__).resolve().parent


def to_forms(mon):
    """Monitor-format constraints -> analyze-format rows ((const, coeffs) triples)."""
    p = int(mon["prime"])
    rows = []
    for c in mon["constraints"]:
        forms = []
        for side in ("L", "R", "O"):
            const, coeff = 0, {}
            for co, w in c[side]:
                co, w = int(co) % p, int(w)
                if w == 0:
                    const = (const + co) % p
                else:
                    coeff[w] = (coeff.get(w, 0) + co) % p
            forms.append((const, {j: v for j, v in coeff.items() if v}))
        rows.append(tuple(forms))
    return p, rows


def row_value(row, a, p):
    (lc, l), (rc, r), (oc, o) = row
    lv = (lc + sum(c * a[j] for j, c in l.items())) % p
    rv = (rc + sum(c * a[j] for j, c in r.items())) % p
    ov = (oc + sum(c * a[j] for j, c in o.items())) % p
    return (lv * rv - ov) % p


def parse_cex(log_path, n):
    """Parse ronin JSONL into verdict and (a, b) witness vectors (or None)."""
    verdict, section = "unknown", None
    first, second = {0: 1}, {0: 1}
    for line in open(log_path):
        line = line.strip()
        if not line:
            continue
        msg = json.loads(line).get("msg", "")
        if "The circuit is underconstrained" in msg:
            verdict = "underconstrained"
        elif "The circuit is properly constrained" in msg or msg.strip() == "safe":
            verdict = "safe"
        elif "inputs:" in msg:
            section = "inputs"
        elif "first possible outputs" in msg or "first internal" in msg:
            section = "first"
        elif "second possible outputs" in msg or "second internal" in msg:
            section = "second"
        else:
            m = re.match(r"^(\d+): (\d+)$", msg.strip())
            if m and section:
                w, v = int(m.group(1)), int(m.group(2))
                if section == "inputs":
                    first[w] = v
                    second[w] = v
                elif section == "first":
                    first[w] = v
                else:
                    second[w] = v
    if verdict != "underconstrained" or len(first) < 2:
        return verdict, None, None
    a = [first.get(i, 0) for i in range(n)]
    b = [second.get(i, 0) for i in range(n)]
    return verdict, a, b


def diagnose(p, rows, witness, fixed, outputs):
    M = [{j: 1} for j in fixed] + jacobian(rows, witness, p)
    pivots, free, expr, _ = echelon(M, len(witness), p)
    nullity = len(free)
    moving_out = [j for j in outputs if expr[j]]
    r_t = dense_rank([[expr[j].get(k, 0) for k in free] for j in moving_out], p) if moving_out else 0
    return nullity, len(moving_out), r_t


def line_direction_status(p, rows, a, v, fixed, outputs):
    """Classify the direction v at witness a: tangent? certified line? moves an output?"""
    if all(x == 0 for x in v):
        return "zero"
    if any(v[j] % p for j in fixed):
        return "moves-conditioned"
    J = jacobian(rows, a, p)
    if any(sum(c * v[j] for j, c in row.items()) % p for row in J):
        return "not-tangent"
    for (lc, l), (rc, r), _ in rows:
        lv = sum(c * v[j] for j, c in l.items()) % p
        rv = sum(c * v[j] for j, c in r.items()) % p
        if lv * rv % p:
            return "tangent-not-line"
    return "certified-line" if any(v[j] % p for j in outputs) else "line-no-output-motion"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--circom", required=True)
    ap.add_argument("--ronin", required=True)
    ap.add_argument("--bench", required=True)
    ap.add_argument("--sets", default="circomlib-cff5ab6,motivating")
    ap.add_argument("--budget", type=float, default=60.0)
    ap.add_argument("--max-constraints", type=int, default=50000)
    args = ap.parse_args()

    bench = Path(args.bench)
    results = []
    for setname in args.sets.split(","):
        for src in sorted((bench / setname).glob("*.circom")):
            if "component main" not in src.read_text():
                continue
            rec = {"set": setname, "circuit": src.stem}
            with tempfile.TemporaryDirectory() as td:
                cp = subprocess.run([args.circom, "--r1cs", "--O0", "-o", td, str(src)],
                                    capture_output=True, text=True, cwd=src.parent)
                if cp.returncode != 0:
                    rec["status"] = "compile-error"
                    results.append(rec)
                    continue
                r1cs_files = list(Path(td).glob("*.r1cs"))
                if not r1cs_files:
                    rec["status"] = "no-r1cs"
                    results.append(rec)
                    continue
                mon = r1cs_iden3.load(str(r1cs_files[0]))
                rec["constraints"] = len(mon["constraints"])
                rec["wires"] = mon["n_wires"]
                if rec["constraints"] > args.max_constraints:
                    rec["status"] = "skipped-size"
                    results.append(rec)
                    continue
                log = Path(td) / "ronin.jsonl"
                t0 = time.perf_counter()
                try:
                    subprocess.run(["./run-ronin", "--timeout", "20000", "--json", str(log),
                                    str(r1cs_files[0])],
                                   capture_output=True, text=True, cwd=args.ronin,
                                   timeout=args.budget)
                    rec["ronin_seconds"] = round(time.perf_counter() - t0, 2)
                except subprocess.TimeoutExpired:
                    rec["status"] = "ronin-wall-timeout"
                    rec["ronin_seconds"] = round(time.perf_counter() - t0, 2)
                    results.append(rec)
                    continue
                verdict, a, b = parse_cex(log, mon["n_wires"]) if log.exists() else ("no-log", None, None)
                rec["ronin_verdict"] = verdict
                if a is None:
                    rec["status"] = verdict
                    results.append(rec)
                    continue

                p, rows = to_forms(mon)
                # iden3 wire classes: [ONE][pubout][pubin][prvin][internal]
                hdr_out = mon["n_public"] - 1  # reader folds out+in into n_public
                # recover output count from the raw header
                outputs = [j for j in range(1, mon["n_public"]) ]
                fixed = [0] + [j for j in range(1, mon["n_public"]) if j not in outputs]
                # ronin's query: outputs = circom main outputs = wires 1..nPubOut.
                # The reader reports n_pub_out inside load(); recover it directly:
                raw = open(r1cs_files[0], "rb").read()
                import struct
                off = 12
                n_pub_out = None
                while off < len(raw):
                    ty, size = struct.unpack_from("<IQ", raw, off)
                    off += 12
                    if ty == 1:
                        fs, = struct.unpack_from("<I", raw, off)
                        _, n_pub_out, _, _ = struct.unpack_from("<IIII", raw, off + 4 + fs)
                        break
                    off += size
                outputs = list(range(1, 1 + (n_pub_out or 0)))
                fixed = [0] + list(range(1 + len(outputs), mon["n_public"]))
                bad_a = any(row_value(r, a, p) for r in rows)
                bad_b = any(row_value(r, b, p) for r in rows)
                rec["witnesses_verified"] = (not bad_a) and (not bad_b)
                if bad_a or bad_b:
                    rec["status"] = "cex-does-not-verify"
                    results.append(rec)
                    continue
                for tag, w in (("a", a), ("b", b)):
                    nullity, mv, r_t = diagnose(p, rows, w, fixed, outputs)
                    rec[f"nullity_{tag}"] = nullity
                    rec[f"moving_outputs_{tag}"] = mv
                    rec[f"rT_outputs_{tag}"] = r_t
                    if 0 < nullity <= 2:
                        analyze_rows = rows
                        ls = line_search(analyze_rows, w, {j: w[j] for j in fixed},
                                         outputs, p)
                        rec[f"line_search_{tag}"] = {
                            "complete": ls.get("complete"),
                            "target_moving_line": ls.get("target_moving_line_exists")}
                v = [(x - y) % p for x, y in zip(b, a)]
                rec["picus_direction_at_a"] = line_direction_status(p, rows, a, v, fixed, outputs)
                rec["status"] = "analysed"
            results.append(rec)
            print(f"{setname}/{src.stem:34s} {rec.get('status'):22s} "
                  f"c={rec.get('constraints','-'):>6} verdict={rec.get('ronin_verdict','-'):16s} "
                  f"nullity(a)={rec.get('nullity_a','-')} rT(a)={rec.get('rT_outputs_a','-')} "
                  f"dir={rec.get('picus_direction_at_a','-')}")

    out = ROOT / "results" / "corpus-line-study.json"
    out.write_text(json.dumps(results, indent=1) + "\n")
    done = [r for r in results if r.get("status") == "analysed"]
    print(f"\n{len(results)} circuits; {len(done)} underconstrained-with-cex analysed; "
          f"results -> {out}")


if __name__ == "__main__":
    main()
