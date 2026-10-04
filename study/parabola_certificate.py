#!/usr/bin/env python3
"""Affine-parabola certificate (Theorem F candidate): exact second-order upgrade.

For R1CS rows f_i = L_i R_i - O_i with homogeneous linear parts l_i, r_i, the
expansion along x(t) = a + t v + t^2 u is exact and splits by degree:

  f_i(x(t)) = f_i(a) + t d_a f_i(v) + t^2 [d_a f_i(u) + Q_i(v)]
              + t^3 [l_i(v) r_i(u) + l_i(u) r_i(v)] + t^4 Q_i(u),

with Q_i(w) = l_i(w) r_i(w).  Given a satisfying a and tangent v (so t^0, t^1
vanish), the t^2 and t^3 conditions are one LINEAR system in u (with u_F = 0),
and a solution u additionally satisfying Q_i(u) = 0 for all i certifies that
the whole parabola lies in the variety.  If the target coordinate x_j(t) =
a_j + t v_j + t^2 u_j is non-constant, it attains at least ceil(p/2) distinct
values over F_p (exactly (p+1)/2 when u_j != 0, p when u_j = 0), and any two
parameters with distinct values give an explicit non-uniqueness pair.

Refusal is not rigidity: the certificate is sufficient only, and the search
over tangent directions v is heuristic (kernel basis plus sampled combinations)
while the search over corrections u is complete for solution spaces of
dimension <= 1 and heuristic above that.  Every emitted certificate is
re-verified by direct substitution at sampled parameters.

Controls: w^2 = 0 must be refused (the t^2 system is inconsistent: 0*u = -v_w^2),
x = w^2 at the origin must certify (u = e_x), and the hyperbola XW = c must be
refused (the combined system forces u into a space where Q never vanishes).
"""
import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from analyze import affine, echelon, jacobian, linear

ROOT = Path(__file__).resolve().parent


def directions_from(expressions, free, n):
    return [[expressions[j].get(t, 0) for j in range(n)] for t in free]


def solve_affine(rows_sparse, rhs, n, p):
    """Solve A u = rhs for sparse dict rows.  Returns (u0, kernel_basis) or None.

    Implemented by eliminating the homogeneous system in n+1 variables
    [A | rhs] (u, s) with the convention s = -1: kernel vectors with nonzero
    last coordinate scale to particular solutions; kernel vectors with zero
    last coordinate form the homogeneous solution space.
    """
    aug = []
    for row, b in zip(rows_sparse, rhs):
        r = dict(row)
        if b % p:
            r[n] = b % p
        aug.append(r)
    pivots, free, expr, _ = echelon(aug, n + 1, p)
    if n not in free:
        # s is pinned: check it is pinned to zero-only solutions
        # expression for coordinate n in terms of free vars:
        if expr[n]:
            # s can be nonzero only via free vars; fall through to generic path
            pass
        else:
            return None  # s forced to 0: A u = rhs has no solution unless rhs=0
    basis = directions_from(expr, free, n + 1)
    particular = None
    kernel = []
    for vec in basis:
        if vec[n] % p:
            inv = pow(-vec[n] % p, -1, p)  # scale so that s = -1  ==> A u = rhs
            particular = [(x * inv) % p for x in vec[:n]]
        else:
            kv = vec[:n]
            if any(kv):
                kernel.append(kv)
    if particular is None:
        if any(b % p for b in rhs):
            return None
        particular = [0] * n
    return particular, kernel


def tonelli(a, p):
    """Square root mod odd prime p, or None."""
    a %= p
    if a == 0:
        return 0
    if pow(a, (p - 1) // 2, p) != 1:
        return None
    if p % 4 == 3:
        return pow(a, (p + 1) // 4, p)
    q, s = p - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (p - 1) // 2, p) != p - 1:
        z += 1
    m, c, t, r = s, pow(z, q, p), pow(a, q, p), pow(a, (q + 1) // 2, p)
    while t != 1:
        i, t2 = 0, t
        while t2 != 1:
            t2 = t2 * t2 % p
            i += 1
        b = pow(c, 1 << (m - i - 1), p)
        m, c, t, r = i, b * b % p, t * b * b % p, r * b % p
    return r


def quad_roots(a2, a1, a0, p):
    """Roots of a2 s^2 + a1 s + a0 over F_p (p odd); None means identically zero."""
    a2, a1, a0 = a2 % p, a1 % p, a0 % p
    if a2 == 0:
        if a1 == 0:
            return None if a0 == 0 else []
        return [(-a0 * pow(a1, -1, p)) % p]
    disc = (a1 * a1 - 4 * a2 * a0) % p
    r = tonelli(disc, p)
    if r is None:
        return []
    inv = pow(2 * a2 % p, -1, p)
    return sorted({((-a1 + r) * inv) % p, ((-a1 - r) * inv) % p})


def parabola_search(rows, a, v, fixed, p):
    """Try to certify a parabola a + tv + t^2 u for tangent v.  Returns u or None,
    plus a completeness flag for the u-search."""
    n = len(a)
    lin_parts = [(l[1], r[1]) for l, r, o in rows]
    J = jacobian(rows, a, p)
    # tangency check
    if any(sum(c * v[j] for j, c in row.items()) % p for row in J):
        return None, True, "not-tangent"
    Qv = [linear((0, l), v, p) * linear((0, r), v, p) % p for l, r in lin_parts]
    # combined linear system in u: J u = -Q(v); fixing rows u_F = 0; polar rows B(v,u)=0
    sys_rows = [dict(row) for row in J]
    rhs = [(-q) % p for q in Qv]
    for j in fixed:
        sys_rows.append({j: 1})
        rhs.append(0)
    for l, r in lin_parts:
        lv, rv = linear((0, l), v, p), linear((0, r), v, p)
        polar = {}
        for j, c in r.items():
            polar[j] = (polar.get(j, 0) + lv * c) % p
        for j, c in l.items():
            polar[j] = (polar.get(j, 0) + rv * c) % p
        polar = {j: c for j, c in polar.items() if c}
        if polar:
            sys_rows.append(polar)
            rhs.append(0)
    sol = solve_affine(sys_rows, rhs, n, p)
    if sol is None:
        return None, True, "t2-t3-system-inconsistent"
    u0, kernel = sol

    def t4_ok(u):
        return all(
            linear((0, l), u, p) * linear((0, r), u, p) % p == 0 for l, r in lin_parts)

    if t4_ok(u0):
        return u0, True, "certified"
    if not kernel:
        return None, True, "t4-fails-unique-u"
    if len(kernel) == 1:
        z = kernel[0]
        root_sets = None
        for l, r in lin_parts:
            lu, lz = linear((0, l), u0, p), linear((0, l), z, p)
            ru, rz = linear((0, r), u0, p), linear((0, r), z, p)
            # Q(u0 + s z) = (lu + s lz)(ru + s rz): quadratic in s
            roots = quad_roots(lz * rz % p, (lu * rz + lz * ru) % p, lu * ru % p, p)
            if roots is None:
                continue
            rs = set(roots)
            root_sets = rs if root_sets is None else (root_sets & rs)
            if not root_sets:
                return None, True, "t4-no-common-root"
        if root_sets:
            s = sorted(root_sets)[0]
            u = [(x + s * y) % p for x, y in zip(u0, z)]
            assert t4_ok(u)
            return u, True, "certified"
        return None, True, "t4-no-common-root"
    # dim >= 2: heuristic probes only
    for s in range(0, 8):
        for z in kernel[:3]:
            u = [(x + s * y) % p for x, y in zip(u0, z)]
            if t4_ok(u):
                return u, False, "certified-heuristic-u"
    return None, False, "t4-unresolved-dim>=2"


def verify_parabola(rows, a, v, u, fixed, p, samples=6):
    import random
    rng = random.Random(20261004)
    for j in fixed:
        assert v[j] % p == 0 and u[j] % p == 0
    for _ in range(samples):
        t = rng.randrange(p)
        x = [(ai + t * vi + t * t * ui) % p for ai, vi, ui in zip(a, v, u)]
        for l, r, o in rows:
            assert (affine(l, x, p) * affine(r, x, p) - affine(o, x, p)) % p == 0
    return True


def kernel_tangents(rows, a, fixed, p, extra_combos=6, special_cap=60):
    """Kernel basis, random combinations, and --- for two-dimensional kernels ---
    the per-row special directions: for each constraint whose linear factors are
    nonzero on the kernel plane, the two projective roots along which that
    factor vanishes.  Certified lines lie among these (u = 0), and curved
    families concentrate on them because they kill one quadratic obstruction."""
    n = len(a)
    M = [{j: 1} for j in fixed] + jacobian(rows, a, p)
    pivots, free, expr, _ = echelon(M, n, p)
    B = directions_from(expr, free, n)
    out = list(B)
    import random
    rng = random.Random(7)
    if len(B) == 2:
        seen = set()
        for l, r, o in rows:
            l0, l1 = linear((0, l[1]), B[0], p), linear((0, l[1]), B[1], p)
            r0, r1 = linear((0, r[1]), B[0], p), linear((0, r[1]), B[1], p)
            for alpha, beta in ((-l1 % p, l0), (-r1 % p, r0)):
                if alpha == 0 and beta == 0:
                    continue
                key = (alpha * pow(beta, -1, p) % p) if beta else "inf"
                if key in seen:
                    continue
                seen.add(key)
                out.append([(alpha * x + beta * y) % p for x, y in zip(B[0], B[1])])
                if len(seen) >= special_cap:
                    break
            if len(seen) >= special_cap:
                break
    for _ in range(extra_combos if len(B) >= 2 else 0):
        c = rng.randrange(1, p)
        out.append([(x + c * y) % p for x, y in zip(B[0], B[1])])
    return out


def controls(p=257):
    # w^2 = 0 at origin: wires (w,); rows: ((0,{0:1}),(0,{0:1}),(0,{}))
    rows = [((0, {0: 1}), (0, {0: 1}), (0, {}))]
    u, complete, status = parabola_search(rows, [0], [1], [], p)
    assert u is None and status == "t2-t3-system-inconsistent", status
    # x = w^2 at origin: wires (w,x); f = w*w - x
    rows = [((0, {0: 1}), (0, {0: 1}), (0, {1: 1}))]
    u, complete, status = parabola_search(rows, [0, 0], [1, 0], [], p)
    assert u is not None and status == "certified", status
    assert verify_parabola(rows, [0, 0], [1, 0], u, [], p)
    # hyperbola XW = 6, Y fixed: wires (X,W,Y); f = X*W - Y; F={Y}
    rows = [((0, {0: 1}), (0, {1: 1}), (0, {2: 1}))]
    a = [2, 3, 6]
    v = [2, -3 % p, 0]
    u, complete, status = parabola_search(rows, a, v, [2], p)
    assert u is None, status
    print(f"controls OK over F_{p}: w^2=0 refused ({'inconsistent'}), "
          f"x=w^2 certified, hyperbola refused ({status})")


def run_export(path, label):
    from analyze import load
    obj, p, rows, a, fixed, targets, digest = load(path)
    assert not any(
        (affine(l, a, p) * affine(r, a, p) - affine(o, a, p)) % p for l, r, o in rows)
    t0 = time.perf_counter()
    found = []
    statuses = {}
    for v in kernel_tangents(rows, a, fixed, p):
        u, complete, status = parabola_search(rows, a, v, fixed, p)
        statuses[status] = statuses.get(status, 0) + 1
        if u is not None:
            moved = [j for j in targets if (v[j] or u[j])]
            if moved:
                verify_parabola(rows, a, v, u, fixed, p)
                found.append({
                    "targets_moved": moved,
                    "v_support": sum(1 for x in v if x),
                    "u_support": sum(1 for x in u if x),
                    "linear_in_target": [j for j in moved if u[j] % p == 0],
                    "u_complete_search": complete,
                })
    rec = {"instance": label, "sha256": digest, "constraints": len(rows),
           "tangents_tried": sum(statuses.values()), "statuses": statuses,
           "parabola_certificates": found,
           "seconds": round(time.perf_counter() - t0, 3)}
    print(f"{label:38s} tangents={rec['tangents_tried']} "
          f"certs={len(found)} statuses={statuses} ({rec['seconds']}s)")
    return rec


def main():
    controls()
    exports = Path(os.environ.get("STUDY_EXPORTS_DIR", ROOT / "exports"))
    out = []
    for name in ["scalar_0_honest", "scalar_0_zero_decomp",
                 "scalar_1_zero_decomp", "scalar_12345_zero_decomp",
                 "scalar_54321_zero_decomp", "sweep_11_both_hints_zero"]:
        f = exports / f"{name}.json"
        if f.exists():
            out.append(run_export(f, name))
    (ROOT / "results" / "parabola-certificates.json").write_text(
        json.dumps(out, indent=1) + "\n")
    print("results -> results/parabola-certificates.json")


if __name__ == "__main__":
    main()
