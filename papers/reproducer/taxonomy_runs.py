#!/usr/bin/env python3
"""Measured runs of the actual Jacobian tool (compose/gnark_jacobian.py) across the
three field-level taxonomy classes, on representative R1CS instances.

CAUGHT  — free hint on a vacuous verification branch (advisory classes #2/#7/#9/#11):
          s*(y-u)=0 with s a selector; at the honest branch s=1 the hint y is pinned to u,
          at the prover-reachable branch s=0 the row is vacuous and y is first-order free.
MISSED (finite multiplicity, within model) — w^2 = x: rigid at each root though 2-valued
          (advisory classes #3/#6: discrete alternative decompositions / sign).
MISSED (range / integer-vs-field, within model) — b*(b-1)=0: the mod-p relation determines b,
          so a mod-p rank test reports "determined"; the exploit lives in the integer/range gap
          the field-level relation does not see (advisory classes #1/#4/#8).
OFF-MODEL (#5, semantic omission) — not runnable: the R1CS is fully satisfied and determined;
          the defect is a missing subgroup/cofactor invariant absent from the encoded relation,
          so there is no field-level freedom for any rank/solver/matroid method to expose.

Uses jacobian_free_wires (pure-Python exact F_p path), no external deps.
"""
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "..", "compose"))
from gnark_jacobian import jacobian_free_wires  # noqa: E402

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
ONE = 0


def run(name, constraints, witness, fixed, target):
    free = jacobian_free_wires(constraints, witness, fixed | {ONE}, P, max(witness) + 1)
    return "free" if target in free else "determined"


def main():
    rows = []

    # --- CAUGHT: vacuous verification / free hint.  wires 0=ONE 1=s 2=u 3=y
    #     constraint  s*(y - u) = 0
    ver = [({1: 1}, {3: 1, 2: P - 1}, {})]
    honest = {0: 1, 1: 1, 2: 7, 3: 7}          # s=1: y must equal u
    degen = {0: 1, 1: 0, 2: 7, 3: 999}         # s=0: row vacuous, y arbitrary
    rows.append(("free hint, verify vacuous", "s*(y-u)=0", "honest s=1",
                 run("caught/honest", ver, honest, {1, 2}, 3), "caught"))
    rows.append(("free hint, verify vacuous", "s*(y-u)=0", "degenerate s=0",
                 run("caught/degen", ver, degen, {1, 2}, 3), "caught"))

    # --- MISSED (finite multiplicity).  wires 0=ONE 1=x 2=w ;  w^2 = x, fix x
    sq = [({2: 1}, {2: 1}, {1: 1})]
    rows.append(("finite multiplicity", "w^2=x", "root w=3 (x=9)",
                 run("mult", sq, {0: 1, 1: 9, 2: 3}, {1}, 2), "missed"))

    # --- MISSED (range / integer-vs-field).  wires 0=ONE 1=b ;  b*(b-1)=0, fix nothing
    boolean = [({1: 1}, {1: 1, 0: P - 1}, {})]
    rows.append(("range / integer-vs-field", "b*(b-1)=0", "b=1",
                 run("range", boolean, {0: 1, 1: 1}, set(), 1), "missed"))

    w = max(len(r[0]) for r in rows)
    print(f"{'class':<{w}}  {'system':<12} {'witness':<16} {'tool verdict':<12} taxonomy")
    print("-" * (w + 56))
    for cls, sysname, wit, verdict, tax in rows:
        print(f"{cls:<{w}}  {sysname:<12} {wit:<16} {verdict:<12} {tax}")

    # assertions: the tool must catch the free hint at the degenerate branch and miss the rest
    caught_degen = rows[1][3] == "free"
    honest_pinned = rows[0][3] == "determined"
    mult_missed = rows[2][3] == "determined"
    range_missed = rows[3][3] == "determined"
    assert caught_degen and honest_pinned and mult_missed and range_missed, "taxonomy not reproduced"
    print("\nOK: caught the free-hint class at the degenerate branch; "
          "missed finite-multiplicity and range as predicted.")
    print("OFF-MODEL (#5 cofactor/torsion): not runnable — the R1CS is fully determined; "
          "no field-level method can expose a missing subgroup invariant.")


if __name__ == "__main__":
    main()
