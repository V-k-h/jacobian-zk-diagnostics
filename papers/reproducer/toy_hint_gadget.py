#!/usr/bin/env python3
"""Synthetic reproducer for the hint-degeneracy witness-locality phenomenon.

A 20-constraint, 20-wire R1CS gadget over the BN254 scalar field reproducing the
0 -> 5 free-target-wire signature of the (anonymized) industrial scalar-multiplication
defect: five hinted outputs y1..y5 are "verified" by rows s*(y_i - u_i) = 0 that are
binding on the honest branch (s = 1) and vacuous on the prover-reachable degenerate
branch (s = 0), which the intended-booleanity constraint s*(s-1) = 0 fails to exclude.

Wires (20):   x, s, u1..u5, y1..y5, b1..b8
Constraints (20):
  1-5   u1 = x*x,  u_{i+1} = u_i * u_i            (binding squaring chain)
  6-10  s * (y_i - u_i) = 0                        (vacuous-able verification)
  11-18 b_i * (b_i - 1) = 0                        (bit booleanity)
  19    sum_i b_i 2^{i-1} - s = 0                  (bit recomposition of s)
  20    s * (s - 1) = 0                            (intended "s = 1"; admits s = 0)

Analysis: conditioned set F = {x}; targets y1..y5. The augmented matrix
M(a) = [J(a); e_x] is reduced exactly over F_p; a target is first-order rigid iff
e_j lies in rowspan M(a), i.e. rank does not grow when e_j is appended.

Expected output: honest witness -> 0 free targets; degenerate witness -> 5 free
targets; plus an explicit second satisfying assignment at the degenerate witness
differing only in y1 (concrete finite-field non-uniqueness).

Also checks the certified-non-uniqueness route (paper: Theorem "certified
finite-field non-uniqueness") at the degenerate witness: the retained generating
set S = {chain rows, booleanity rows, s(s-1), e_x} has full row rank 15 equal to
rank M(a) (so the dropped rows add nothing to the row span), each dropped row g
carries an explicit local-redundancy identity w*g = sum q_i f_i with w nonzero at
the witness (verified as a polynomial identity by exact random evaluation,
Schwartz-Zippel), and the Lang-Weil budget 32*delta^{13/3} <= p holds for
delta <= 2^14, certifying >= p/2^15 distinct values of each target.

No dependencies beyond the Python standard library. Exact arithmetic throughout.
"""

P = 21888242871839275222246405745257275088548364400416034343698204186575808495617

# wire indices
X = 0
S = 1
U = list(range(2, 7))    # u1..u5
Y = list(range(7, 12))   # y1..y5
B = list(range(12, 20))  # b1..b8
NW = 20

# each constraint: (L, R, O) with L/R/O = (dict wire->coeff, const)
def constraints():
    cs = []
    # 1-5: squaring chain
    cs.append((({X: 1}, 0), ({X: 1}, 0), ({U[0]: 1}, 0)))
    for i in range(4):
        cs.append((({U[i]: 1}, 0), ({U[i]: 1}, 0), ({U[i + 1]: 1}, 0)))
    # 6-10: s * (y_i - u_i) = 0
    for i in range(5):
        cs.append((({S: 1}, 0), ({Y[i]: 1, U[i]: -1}, 0), ({}, 0)))
    # 11-18: booleanity b_i * (b_i - 1) = 0
    for b in B:
        cs.append((({b: 1}, 0), ({b: 1}, -1), ({}, 0)))
    # 19: (1) * (sum b_i 2^{i-1} - s) = 0
    cs.append((({}, 1), ({**{b: 1 << k for k, b in enumerate(B)}, S: -1}, 0), ({}, 0)))
    # 20: s * (s - 1) = 0
    cs.append((({S: 1}, 0), ({S: 1}, -1), ({}, 0)))
    return cs


def lin_eval(lin, a):
    d, c = lin
    return (sum(v * a[w] for w, v in d.items()) + c) % P


def check_witness(cs, a):
    for i, (L, R, O) in enumerate(cs):
        if (lin_eval(L, a) * lin_eval(R, a) - lin_eval(O, a)) % P != 0:
            raise AssertionError(f"constraint {i + 1} violated")


def jac_rows(cs, a):
    rows = []
    for L, R, O in cs:
        la, ra = lin_eval(L, a), lin_eval(R, a)
        row = [0] * NW
        for w, v in L[0].items():
            row[w] = (row[w] + v * ra) % P
        for w, v in R[0].items():
            row[w] = (row[w] + la * v) % P
        for w, v in O[0].items():
            row[w] = (row[w] - v) % P
        rows.append(row)
    return rows


def rank(rows):
    m = [r[:] for r in rows if any(r)]
    r, cols = 0, NW
    for c in range(cols):
        piv = next((i for i in range(r, len(m)) if m[i][c]), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], P - 2, P)
        m[r] = [(v * inv) % P for v in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c]:
                f = m[i][c]
                m[i] = [(m[i][j] - f * m[r][j]) % P for j in range(cols)]
        r += 1
    return r


def analyse(name, a, cs):
    check_witness(cs, a)
    e_x = [0] * NW
    e_x[X] = 1
    M = jac_rows(cs, a) + [e_x]          # conditioned set F = {x}
    base = rank(M)
    free = []
    for t in Y:
        e_t = [0] * NW
        e_t[t] = 1
        if rank(M + [e_t]) != base:      # e_t not in rowspan -> infinitesimally free
            free.append(t)
    print(f"{name}: rank(M) = {base}, free target wires = {len(free)} "
          f"({['y%d' % (Y.index(t) + 1) for t in free]})")
    return len(free)


def poly_eval(cs_i, a):
    """Value of constraint polynomial f_i = (L.a)(R.a) - (O.a) at an arbitrary point."""
    L, R, O = cs_i
    return (lin_eval(L, a) * lin_eval(R, a) - lin_eval(O, a)) % P


def certificate_checks(cs, degen):
    """Theorem 'certified finite-field non-uniqueness' at the degenerate witness.

    Retained set S: chain rows (1-5), booleanity rows (11-18), s(s-1) (20), e_x.
    Dropped: the five verification rows s*(y_i - u_i) and the recomposition row.
    """
    import random
    rng = random.Random(2026)

    # 1. local-redundancy identities, checked as polynomial identities at random
    #    points (degree <= 11, so one honest point already gives SZ error <= 11/p;
    #    we use eight).
    for _ in range(8):
        a = [rng.randrange(P) for _ in range(NW)]
        s, bs = a[S], [a[b] for b in B]
        # (s-1) * [s(y_i-u_i)] = (y_i-u_i) * [s(s-1)]
        for i in range(5):
            lhs = (s - 1) * poly_eval(cs[5 + i], a) % P
            rhs = (a[Y[i]] - a[U[i]]) * poly_eval(cs[19], a) % P
            assert lhs == rhs, "verification-row redundancy identity failed"
        # w*g = sum_j 2^{j-1} (s-1) prod_{k!=j}(b_k-1) * [b_j(b_j-1)]
        #       - prod_k(b_k-1) * [s(s-1)],  w = (s-1) prod_k(b_k-1)
        w = (s - 1) % P
        for bv in bs:
            w = w * (bv - 1) % P
        g = poly_eval(cs[18], a)
        prod_all = 1
        for bv in bs:
            prod_all = prod_all * (bv - 1) % P
        rhs = (-prod_all * poly_eval(cs[19], a)) % P
        for j, bv in enumerate(bs):
            prod_not_j = 1
            for k, bk in enumerate(bs):
                if k != j:
                    prod_not_j = prod_not_j * (bk - 1) % P
            rhs = (rhs + (1 << j) * (s - 1) * prod_not_j * poly_eval(cs[10 + j], a)) % P
        assert w * g % P == rhs, "recomposition-row redundancy identity failed"

    # w(a) != 0 at the degenerate witness for every dropped row's multiplier
    s0, bs0 = degen[S], [degen[b] for b in B]
    assert (s0 - 1) % P != 0
    w0 = (s0 - 1) % P
    for bv in bs0:
        w0 = w0 * (bv - 1) % P
    assert w0 != 0

    # 2. retained rows have full row rank equal to rank M(a): kernel unchanged
    e_x = [0] * NW
    e_x[X] = 1
    retained_idx = list(range(0, 5)) + list(range(10, 18)) + [19]
    all_rows = jac_rows(cs, degen)
    m_s = [all_rows[i] for i in retained_idx] + [e_x]
    assert rank(m_s) == len(m_s) == 15, "retained set not full-rank"
    assert rank(all_rows + [e_x]) == 15, "dropped rows enlarge the row span"

    # 3. Lang-Weil budget: delta <= 2^{m2}, m2 = 14 quadratic retained rows;
    #    32*delta^{13/3} <= p  <=>  32^3 * delta^13 <= p^3; side condition
    #    2(d+1)delta^2 < p with d = 20 - 15 = 5.
    m2, d = 14, NW - 15
    delta = 1 << m2
    assert 32 ** 3 * delta ** 13 <= P ** 3, "Lang-Weil budget violated"
    assert 2 * (d + 1) * delta ** 2 < P, "Cafure-Matera side condition violated"
    print(f"certificate: retained rank 15/15, redundancy identities verified, "
          f"budget ok (m2={m2}, d={d}); certified >= p/2^{m2 + 1} distinct values "
          f"per target")


def main():
    cs = constraints()
    x = 3
    u = [pow(x, 2 ** (i + 1), P) for i in range(5)]

    honest = [0] * NW
    honest[X], honest[S] = x, 1
    for i in range(5):
        honest[U[i]], honest[Y[i]] = u[i], u[i]
    honest[B[0]] = 1                      # bits of s = 1
    n_honest = analyse("honest    (s=1, bits=1000_0000)", honest, cs)

    degen = [0] * NW
    degen[X], degen[S] = x, 0             # s = 0, all bits = 0
    for i in range(5):
        degen[U[i]], degen[Y[i]] = u[i], (7 + 4 * i) % P   # hinted y_i unconstrained
    n_degen = analyse("degenerate(s=0, bits=0000_0000)", degen, cs)
    certificate_checks(cs, degen)

    # concrete second witness at the degenerate branch: change y1 only
    second = degen[:]
    second[Y[0]] = (second[Y[0]] + 1) % P
    check_witness(cs, second)
    print("second witness: y1 -> y1+1 also satisfies all constraints "
          "(concrete finite-field non-uniqueness)")

    assert n_honest == 0 and n_degen == 5, "signature 0 -> 5 not reproduced"
    print("OK: reproduces the 0 -> 5 free-target signature")


if __name__ == "__main__":
    main()
