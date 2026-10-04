"""Reference checks for the added R1CS propositions; Python standard library only.

Run: python3 certificate_checker.py
This is an independent small-system reference, not the paper's gnark exporter,
benchmark harness, certificate-search algorithm, or Lean development.
The caller must supply a PRIME p and the COMPLETE circuit and conditioned set.
Affine forms are (constant, {zero-based coordinate: coefficient}).
"""
from itertools import product, combinations
import random


def linear(form, x, p):
    return sum(c * x[j] for j, c in form[1].items()) % p


def affine(form, x, p):
    return (form[0] + linear(form, x, p)) % p


def values(rows, x, p):
    return [(affine(l, x, p) * affine(r, x, p) - affine(o, x, p)) % p
            for l, r, o in rows]


def line_certificate(rows, a, v, fixed, target, p):
    """Deterministically verify the sufficient affine-line conditions.

    Return an explicit second witness, or None when the supplied vector fails.
    `fixed` maps conditioned coordinates to their required values.
    No search completeness, prime validation, or file-format binding is claimed.
    """
    if p < 2 or len(a) != len(v) or not 0 <= target < len(a):
        raise ValueError('Invalid dimension, target, or modulus')
    if any(not 0 <= j < len(a) for j in fixed):
        raise ValueError('Conditioned coordinate out of bounds')
    if any(not 0 <= j < len(a) for row in rows for form in row for j in form[1]):
        raise ValueError('Constraint coordinate out of bounds')
    if any((a[j] - u) % p or v[j] % p for j, u in fixed.items()):
        return None
    if not v[target] % p or any(values(rows, a, p)):
        return None
    for l, r, o in rows:
        lv, rv = linear(l, v, p), linear(r, v, p)
        derivative = lv * affine(r, a, p) + affine(l, a, p) * rv - linear(o, v, p)
        if derivative % p or lv * rv % p:
            return None
    b = [(x + y) % p for x, y in zip(a, v)]
    # Independent final re-evaluation of every original constraint.
    if any(values(rows, b, p)) or any((b[j] - u) % p for j, u in fixed.items()):
        raise AssertionError('Certificate implementation inconsistency')
    return b


def rank(matrix, p):
    """Dense reference rank over a caller-supplied prime field."""
    a = [[x % p for x in row] for row in matrix]
    if not a:
        return 0
    if any(len(row) != len(a[0]) for row in a):
        raise ValueError('Ragged matrix')
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        inv = pow(a[r][c], -1, p)
        a[r] = [(x * inv) % p for x in a[r]]
        for i in range(r + 1, len(a)):
            q = a[i][c]
            a[i] = [(x - q*y) % p for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def target_dimension(matrix, targets, n, p):
    """rank([M; E_T]) - rank(M), using dense reference elimination."""
    if any(len(row) != n for row in matrix):
        raise ValueError('Incorrect column count')
    if any(not 0 <= j < n for j in targets):
        raise ValueError('Target out of bounds')
    fixing = [[int(i == j) for i in range(n)] for j in targets]
    return rank(list(matrix) + fixing, p) - rank(matrix, p)


def self_test():
    z = (0, {})
    one = (1, {})
    # Guarded freedom, a non-radical false alarm, and a curved hyperbola.
    for p in (2, 3, 5, 7):
        guard = [((0, {0: 1}), (0, {1: 1}), z)]
        assert line_certificate(guard, [0, 0], [0, 1], {0: 0}, 1, p) == [0, 1]
        assert line_certificate(guard, [0, 0], [0, 1], {1: 0}, 1, p) is None
        square = [((0, {0: 1}), (0, {0: 1}), z)]
        assert line_certificate(square, [0], [1], {}, 0, p) is None
        hyperbola = [((0, {0: 1}), (0, {1: 1}), one)]
        assert line_certificate(hyperbola, [1, 1], [1, -1], {}, 0, p) is None
    # The paper's 20-wire synthetic gadget, including all 20 constraints.
    p = 257
    x, s = 0, 1
    us, ys, bs = list(range(2, 7)), list(range(7, 12)), list(range(12, 20))
    rows = []
    prev = x
    a = [0]*20
    a[x] = 3
    for u in us:
        rows.append(((0, {prev: 1}), (0, {prev: 1}), (0, {u: 1})))
        a[u] = a[prev]**2 % p
        prev = u
    rows += [((0, {s: 1}), (0, {y: 1, u: -1}), z) for y, u in zip(ys, us)]
    rows += [((0, {b: 1}), (-1, {b: 1}), z) for b in bs]
    rows.append(((0, {**{b: 2**i for i, b in enumerate(bs)}, s: -1}), one, z))
    rows.append(((0, {s: 1}), (-1, {s: 1}), z))
    assert len(rows) == 20 and not any(values(rows, a, p))
    for y in ys:
        v = [int(i == y) for i in range(20)]
        assert line_certificate(rows, a, v, {x: 3}, y, p) is not None
        attained = set()
        for t in range(p):
            point = [(ai+t*vi) % p for ai, vi in zip(a, v)]
            assert not any(values(rows, point, p))
            attained.add(point[y])
        assert len(attained) == p
    # Exhaustively check all one-variable R1CS rows, points and directions over F_3.
    p = 3
    forms = [(c, {0: k}) for c, k in product(range(p), repeat=2)]
    tested = 0
    for row in product(forms, repeat=3):
        for aa, vv in product(range(p), repeat=2):
            accepted = line_certificate([row], [aa], [vv], {}, 0, p) is not None
            entire_line = vv != 0 and all(not any(values([row], [(aa+t*vv) % p], p))
                                          for t in range(p))
            assert accepted == entire_line
            tested += 1
    # Compare projected rank with enumerated kernel images and minimum fixing sets.
    rng = random.Random(90210)
    cases = 0
    for p in (2, 3, 5):
        n = 3
        for _ in range(30):
            matrix = [[rng.randrange(p) for _ in range(n)] for _ in range(rng.randrange(4))]
            kernel = [v for v in product(range(p), repeat=n)
                      if all(sum(x*y for x, y in zip(row, v)) % p == 0 for row in matrix)]
            for mask in range(1 << n):
                ts = [i for i in range(n) if mask & (1 << i)]
                d = target_dimension(matrix, ts, n, p)
                assert len({tuple(v[j] for j in ts) for v in kernel}) == p**d
                minimum = next(k for k in range(len(ts)+1)
                    if any(all(any(v[j] for j in subset) or all(v[j] == 0 for j in ts)
                               for v in kernel) for subset in combinations(ts, k)))
                assert minimum == d
                cases += 1
    print(f'PASS: {tested} exhaustive affine-line cases; {cases} projected-dimension/minimum-fixing cases;')
    print('      guard/square/hyperbola controls; all 257 parameters for each of 5 synthetic-gadget directions.')


if __name__ == '__main__':
    self_test()
