#!/usr/bin/env python3
"""Upgrade Jacobian flags to a concrete second-witness certificate.

At the degenerate (halfGCD-zeroed) witness of the gnark 0.14.0 twisted-Edwards
ScalarMul gadget, the augmented-Jacobian diagnostic flags five advice wires as
first-order free. A tangent direction is not yet a counterexample, and naive
single-wire perturbation is rejected: the freedom is coupled (two free
parameters propagating through three live rows). This script performs the
paper's second-witness construction on the slice:

  1. collect the LIVE rows — constraints still involving a flagged wire after
     every other wire is substituted with its witness value (all other rows
     touching the flagged wires are vacuous 0*(...)=0 on this branch);
  2. re-seed one flagged wire (+1), keep the other free choices, and propagate
     through live rows that become univariate-linear in one remaining unknown
     (L, R, or O side), taking field inverses as needed;
  3. re-check EVERY R1CS constraint on the rebuilt assignment and confirm the
     declared inputs are untouched.

A success is an exact two-witness counterexample: same public scalar, a
different accepted result. Exit 0 on success.

Usage: second_witness_flagged.py <r1cs.json> <wit.json> <wire_id> [wire_id...]
"""
import json
import sys


def load(r1cs_path, wit_path):
    d = json.load(open(r1cs_path))
    p = int(d["prime"])

    def tm(lst):
        m = {}
        for coef, wid in lst:
            m[int(wid)] = (m.get(int(wid), 0) + int(coef)) % p
        return m

    cons = [(tm(c["L"]), tm(c["R"]), tm(c["O"])) for c in d["constraints"]]
    w = json.load(open(wit_path))
    wit = [int(v) % p for v in w["values"]]
    return d, p, cons, wit


def violations(cons, wit, p):
    def ev(side):
        return sum(c * wit[i] for i, c in side.items()) % p
    return [k for k, (L, R, O) in enumerate(cons)
            if (ev(L) * ev(R) - ev(O)) % p]


def split(side, known, flagged, p):
    """Return (constant part over known wires, {flagged wire: coef})."""
    const, syms = 0, {}
    for wid, c in side.items():
        if wid in flagged and wid not in known:
            syms[wid] = c
        else:
            const = (const + c * known[wid]) % p
    return const, syms


def propagate(cons, live, known, flagged, p):
    """Solve live rows that are univariate-linear in one unknown; fixpoint."""
    changed = True
    while changed:
        changed = False
        for k in live:
            L, R, O = cons[k]
            lc, ls = split(L, known, flagged, p)
            rc, rs = split(R, known, flagged, p)
            oc, os_ = split(O, known, flagged, p)
            unknowns = set(ls) | set(rs) | set(os_)
            if len(unknowns) != 1:
                continue
            (u,) = unknowns
            # (lc + a*u)(rc + b*u) = oc + c*u ; linear when a*b == 0
            a, b, c = ls.get(u, 0), rs.get(u, 0), os_.get(u, 0)
            if a and b:
                continue  # genuinely quadratic in u; out of scope here
            lin = (a * rc + b * lc - c) % p
            rhs = (oc - lc * rc) % p
            if lin == 0:
                continue  # u free or inconsistent in this row; let recheck rule
            known[u] = rhs * pow(lin, -1, p) % p
            changed = True


def main():
    r1cs_path, wit_path = sys.argv[1], sys.argv[2]
    flagged = set(int(x) for x in sys.argv[3:])
    d, p, cons, wit = load(r1cs_path, wit_path)
    nfix = d["n_public"] + d["n_secret"]
    assert not violations(cons, wit, p), "base witness does not satisfy the R1CS"
    assert all(x >= nfix for x in flagged), "flagged wires must be advice wires"

    # live rows: still symbolic in a flagged wire after substituting the rest
    known_base = {i: v for i, v in enumerate(wit) if i not in flagged}
    live = []
    for k, (L, R, O) in enumerate(cons):
        if not (set(L) | set(R) | set(O)) & flagged:
            continue
        lc, ls = split(L, known_base, flagged, p)
        rc, rs = split(R, known_base, flagged, p)
        oc, os_ = split(O, known_base, flagged, p)
        # vacuous on this branch if it holds identically with one side zero
        if not ls and not rs and not os_:
            continue
        if lc == 0 and not ls and not os_ and oc == 0:
            continue  # 0 * (anything) = 0
        if rc == 0 and not rs and not os_ and oc == 0:
            continue  # (anything) * 0 = 0
        live.append(k)
    print(f"{len(live)} live rows on the degenerate branch: {live}")

    for seed in sorted(flagged):
        known = {i: v for i, v in enumerate(wit) if i not in flagged}
        known[seed] = (wit[seed] + 1) % p
        # alternate: propagate what the live rows force, and when they stall,
        # pin the next still-free flagged wire to its old value (a free choice)
        while True:
            propagate(cons, live, known, flagged, p)
            unassigned = sorted(x for x in flagged if x not in known)
            if not unassigned:
                break
            known[unassigned[0]] = wit[unassigned[0]]
        cand = [known[i] for i in range(len(wit))]
        if violations(cons, cand, p):
            print(f"seed wire {seed}: propagation did not close — trying next seed")
            continue
        diff = [i for i in range(len(wit)) if cand[i] != wit[i]]
        assert all(cand[i] == wit[i] for i in range(nfix))
        print(f"seed wire {seed}: SECOND WITNESS CONFIRMED — all {len(cons)} "
              f"constraints satisfied, inputs identical, wires changed: {diff}")
        return 0
    print("no seed produced a second witness (freedom may need joint re-solve)")
    return 1


if __name__ == "__main__":
    sys.exit(main())
