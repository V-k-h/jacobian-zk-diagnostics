#!/usr/bin/env python3
"""Lexicographic Groebner bases on slices: the computational realization of the
paper's elimination certificate (lem:elimcert) on the slices its pipeline isolates.

The slice discipline (cor:slicelift) freezes every coordinate outside a small set
W at the sampled witness and keeps every constraint whose support meets W, so the
resulting polynomial system lives in |W| variables --- small enough for exact
Buchberger over F_p with a lexicographic order.  For a target x_j in W, ordering
x_j last makes GB ∩ F_p[x_j] the elimination ideal: a univariate generator of
degree d is a COMPLETE multiplicity bound for the slice (lem:elimcert, with a
scalar leading coefficient, so the nonvanishing condition is immediate), while a
zero elimination ideal proves the target projection is dominant on the slice
variety --- over the algebraic closure all but finitely many values are attained.
Conclusions are slice-conditional exactly as cor:slicelift states.

Controls: the coupled system {w+u=5, wu=6} must produce w^2-5w+6 (bound 2);
w^2=x with x frozen must produce degree 2; the reproducer's degenerate slice
(every row vacuous after substitution) must produce the zero ideal.

Real instance: the halfGCD-zeroed branch of the query-aware ScalarMul export,
whose 7-coordinate slice refuses both the line and parabola certificates.
"""
import json
import os
import sys
import time
from itertools import combinations
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze import affine, echelon, jacobian, load

ROOT = Path(__file__).resolve().parent


# ---------- exact multivariate polynomials over F_p (lex order) ----------

def lex_key(mon):
    return mon


def poly_normal(poly, p):
    return {m: c % p for m, c in poly.items() if c % p}


def leading(poly):
    return max(poly.keys())


def mon_mul(m1, m2):
    return tuple(a + b for a, b in zip(m1, m2))


def mon_divides(m1, m2):
    return all(a <= b for a, b in zip(m1, m2))


def mon_div(m1, m2):
    return tuple(a - b for a, b in zip(m1, m2))


def mon_lcm(m1, m2):
    return tuple(max(a, b) for a, b in zip(m1, m2))


def poly_mul_term(poly, mon, coeff, p):
    return {mon_mul(m, mon): (c * coeff) % p for m, c in poly.items()}


def poly_sub(p1, p2, p):
    out = dict(p1)
    for m, c in p2.items():
        out[m] = (out.get(m, 0) - c) % p
    return {m: c for m, c in out.items() if c}


def reduce_poly(poly, basis, p):
    poly = poly_normal(poly, p)
    changed = True
    while poly and changed:
        changed = False
        lm, lc = leading(poly), poly[leading(poly)]
        for g in basis:
            glm = leading(g)
            if mon_divides(glm, lm):
                factor = (lc * pow(g[glm], -1, p)) % p
                poly = poly_sub(poly, poly_mul_term(g, mon_div(lm, glm), factor, p), p)
                changed = True
                break
    return poly


def buchberger(gens, p, max_basis=400, max_pairs=20000):
    basis = []
    for g in gens:
        g = reduce_poly(g, basis, p)
        if g:
            basis.append(g)
    pairs = list(combinations(range(len(basis)), 2))
    processed = 0
    while pairs:
        if len(basis) > max_basis or processed > max_pairs:
            return None  # honest failure: blow-up guard
        i, j = pairs.pop()
        processed += 1
        gi, gj = basis[i], basis[j]
        li, lj = leading(gi), leading(gj)
        if all(a == 0 or b == 0 for a, b in zip(li, lj)):
            continue  # Buchberger's coprimality criterion
        l = mon_lcm(li, lj)
        s = poly_sub(
            poly_mul_term(gi, mon_div(l, li), pow(gi[li], -1, p), p),
            poly_mul_term(gj, mon_div(l, lj), pow(gj[lj], -1, p), p), p)
        s = reduce_poly(s, basis, p)
        if s:
            basis.append(s)
            pairs.extend((k, len(basis) - 1) for k in range(len(basis) - 1))
    # interreduce
    out = []
    for i, g in enumerate(basis):
        r = reduce_poly(g, [h for k, h in enumerate(basis) if k != i and h], p)
        if r:
            lc = r[leading(r)]
            out.append({m: (c * pow(lc, -1, p)) % p for m, c in r.items()})
    # dedupe
    seen, final = set(), []
    for g in sorted(out, key=lambda g: leading(g)):
        key = tuple(sorted(g.items()))
        if key not in seen:
            seen.add(key)
            final.append(g)
    return final


def elimination_univariate(basis, var_index, nvars):
    """Generators of GB ∩ F_p[x_{var_index}] (lex with that variable last)."""
    best = None
    for g in basis:
        if all(m[k] == 0 for m in g for k in range(nvars) if k != var_index):
            d = max(m[var_index] for m in g)
            if best is None or d < best[0]:
                best = (d, g)
    return best


# ---------- slice construction (cor:slicelift) ----------

def build_slice(rows, a, W, p):
    """Substitute frozen coordinates, keep rows meeting W, as polynomials in W."""
    idx = {w: k for k, w in enumerate(W)}
    nv = len(W)
    polys = []
    for l, r, o in rows:
        if not (set(l[1]) | set(r[1]) | set(o[1])) & set(W):
            continue

        def lin(form):
            const, coeff = form
            c = const
            lincoef = [0] * nv
            for j, co in coeff.items():
                if j in idx:
                    lincoef[idx[j]] = (lincoef[idx[j]] + co) % p
                else:
                    c = (c + co * a[j]) % p
            return c % p, lincoef

        lc_, lv = lin(l)
        rc_, rv = lin(r)
        oc_, ov = lin(o)
        poly = {}

        def add(mon, c):
            if c % p:
                poly[mon] = (poly.get(mon, 0) + c) % p

        zero = tuple([0] * nv)
        add(zero, lc_ * rc_ - oc_)
        for k in range(nv):
            e = tuple(1 if t == k else 0 for t in range(nv))
            add(e, lc_ * rv[k] + rc_ * lv[k] - ov[k])
        for k1 in range(nv):
            for k2 in range(nv):
                if lv[k1] and rv[k2]:
                    e = tuple((1 if t == k1 else 0) + (1 if t == k2 else 0)
                              for t in range(nv))
                    add(e, lv[k1] * rv[k2])
        poly = poly_normal(poly, p)
        if poly:
            polys.append(poly)
    # dedupe
    seen, out = set(), []
    for g in polys:
        key = tuple(sorted(g.items()))
        if key not in seen:
            seen.add(key)
            out.append(g)
    return out


def analyse_slice(rows, a, W, target, p, label):
    """Lex GB of the slice with `target` ordered last; report elimination data."""
    # order W so that target is the last variable (lex eliminates the others)
    Wo = [w for w in W if w != target] + [target]
    polys = build_slice(rows, a, Wo, p)
    t0 = time.perf_counter()
    gb = buchberger(polys, p)
    dt = round(time.perf_counter() - t0, 3)
    if gb is None:
        print(f"{label}: GB blow-up guard hit ({len(polys)} gens)")
        return {"label": label, "status": "gb-abort", "generators": len(polys)}
    tidx = len(Wo) - 1
    uni = elimination_univariate(gb, tidx, len(Wo))
    rec = {"label": label, "slice_vars": len(Wo), "slice_generators": len(polys),
           "gb_size": len(gb), "gb_seconds": dt}
    if uni is None:
        rec["elimination_ideal"] = "zero"
        rec["conclusion"] = ("target projection dominant on the slice variety: "
                             "all but finitely many values attained over the closure")
    else:
        d, g = uni
        coeffs = {m[tidx]: c for m, c in g.items()}
        rec["elimination_ideal"] = {"degree": d,
                                    "poly": {str(k): str(v) for k, v in sorted(coeffs.items())}}
        rec["conclusion"] = f"complete slice multiplicity bound {d} (lem:elimcert, scalar leading coefficient)"
    print(f"{label}: vars={rec['slice_vars']} gens={rec['slice_generators']} "
          f"gb={rec['gb_size']} ({dt}s) -> {rec['conclusion']}")
    return rec


# ---------- controls ----------

def controls(p=10007):
    # coupled system: w + u = 5, wu = 6; no frozen coords; target w
    rows = [((-5 % p, {0: 1, 1: 1}), (0, {}), (0, {})),  # (w+u-5)*0 - 0? -- encode as L*R-O with L affine, R=1
            ]
    # encode linear row as (w+u-5)*1 = 0 and product row as w*u - 6 = 0
    rows = [((-5 % p, {0: 1, 1: 1}), (1, {}), (0, {})),
            ((0, {0: 1}), (0, {1: 1}), (6 % p, {}))]
    a = [2, 3]
    rec = analyse_slice(rows, a, [0, 1], 0, p, "control coupled {w+u=5, wu=6} target w")
    assert rec["elimination_ideal"]["degree"] == 2
    poly = rec["elimination_ideal"]["poly"]
    assert poly == {"0": "6", "1": str(p - 5), "2": "1"}, poly  # w^2 - 5w + 6
    # w^2 = x with x frozen at 1; target w
    rows = [((0, {0: 1}), (0, {0: 1}), (0, {1: 1}))]
    a = [1, 1]
    rec = analyse_slice(rows, a, [0], 0, p, "control w^2=x (x frozen) target w")
    assert rec["elimination_ideal"]["degree"] == 2
    # reproducer degenerate slice: rows s(y-u)=0 with s,u frozen at s=0 -> vacuous
    rows = [((0, {0: 1}), (0, {1: 1, 2: -1 % p}), (0, {}))]  # s*(y-u)
    a = [0, 7, 3]  # s=0 frozen, y target, u frozen
    rec = analyse_slice(rows, a, [1], 1, p, "control vacuous guard slice target y")
    assert rec["elimination_ideal"] == "zero"
    print("controls OK")


# ---------- the real curved slice ----------

def run_scalar_slice(name):
    path = Path(os.environ.get("STUDY_EXPORTS_DIR", ROOT / "exports")) / f"{name}.json"
    obj, p, rows, a, fixed, targets, digest = load(path)
    assert not any(
        (affine(l, a, p) * affine(r, a, p) - affine(o, a, p)) % p for l, r, o in rows)
    M = [{j: 1} for j in fixed] + jacobian(rows, a, p)
    pivots, free, expr, _ = echelon(M, len(a), p)
    W = sorted(j for j in range(len(a)) if expr[j])  # the moving coordinates
    out = []
    for target in targets:
        if target in W:
            rec = analyse_slice(rows, a, W, target, p,
                                f"{name} slice W={W} target wire {target}")
            rec["sha256"] = digest
            out.append(rec)
    return out


def main():
    controls()
    results = []
    for name in ["scalar_12345_zero_decomp", "scalar_1_zero_decomp",
                 "scalar_54321_zero_decomp", "scalar_0_zero_decomp"]:
        results.extend(run_scalar_slice(name))
    (ROOT / "results" / "groebner-slices.json").write_text(
        json.dumps(results, indent=1) + "\n")
    print("results -> results/groebner-slices.json")


if __name__ == "__main__":
    main()
