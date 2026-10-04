#!/usr/bin/env python3
"""gnark_sparse — sparse exact-F_p rank / nullspace-support, to push the Jacobian
determinacy oracle past the dense O(n^3) ceiling (~6k wires) to the EdDSA circuits
(21k+ wires).

R1CS Jacobians are very sparse (each constraint touches a handful of wires) and
near-triangular (each internal wire is introduced by one constraint), so sparse
Gaussian elimination with fill-reducing (Markowitz) pivoting stays near-linear.
Unlike Wiedemann (rank only), echelon form yields the NULLSPACE SUPPORT directly —
the set of under-determined wires — which is what the determinacy decomposition needs.

  sparse_support(rows, ncols, p) -> (rank, undetermined_cols:set)

Rows are dicts {col: val}. `undetermined_cols` = columns that can be nonzero in some
null vector of the matrix (free columns plus pivot columns depending on a free one).
"""
import heapq


def _elim(rows, ncols, p):
    """Sparse forward elimination to echelon form with Markowitz pivoting.
    Returns (pivot_rows: dict pivcol->row_dict, free_cols: set, pivot_order: list)."""
    rows = [dict(r) for r in rows if r]                 # live rows (drop empties)
    col_rows = {}                                       # col -> set(row idx) live
    for i, r in enumerate(rows):
        for c in r:
            col_rows.setdefault(c, set()).add(i)
    alive = [True] * len(rows)
    pivots = {}                                         # pivcol -> reduced row dict
    order = []
    # bucket columns by current row-count for cheap min-degree selection
    def col_deg(c):
        return len(col_rows.get(c, ()))
    remaining_cols = set(c for c in col_rows if col_rows[c])
    heap = [(col_deg(c), c) for c in remaining_cols]
    heapq.heapify(heap)

    while heap:
        deg, c = heapq.heappop(heap)
        rs = col_rows.get(c)
        if not rs:
            continue
        if deg != len(rs):                              # stale heap entry
            heapq.heappush(heap, (len(rs), c))
            continue
        if c in pivots:
            continue
        # Markowitz: among rows containing c, pick the sparsest as pivot row
        pr = min(rs, key=lambda i: len(rows[i]))
        prow = rows[pr]
        inv = pow(prow[c] % p, -1, p)
        prow = {k: (v * inv) % p for k, v in prow.items()}
        pivots[c] = prow
        order.append(c)
        alive[pr] = False
        for cc in prow:                                 # detach pivot row from incidence
            col_rows.get(cc, set()).discard(pr)
        # eliminate c from every other live row containing it
        for i in list(col_rows.get(c, ())):
            if not alive[i]:
                continue
            ri = rows[i]
            f = ri.get(c, 0) % p
            if f == 0:
                continue
            for k, v in prow.items():
                nv = (ri.get(k, 0) - f * v) % p
                if nv:
                    if k not in ri:
                        col_rows.setdefault(k, set()).add(i)
                    ri[k] = nv
                elif k in ri:
                    del ri[k]
                    col_rows.get(k, set()).discard(i)
            # c is now zero in ri
        col_rows[c] = set()
        # push any columns whose degree changed (touched by fill) — lazily via staleness
        for k in prow:
            if k != c and k not in pivots and col_rows.get(k):
                heapq.heappush(heap, (len(col_rows[k]), k))
    free_cols = set(c for c in range(ncols) if c not in pivots)
    return pivots, free_cols, order


def sparse_support(rows, ncols, p):
    """Rank + the set of columns in the support of the nullspace (undetermined wires)."""
    pivots, free_cols, order = _elim(rows, ncols, p)
    rank = len(pivots)
    # After forward elimination each pivot row references only LATER-pivoted columns
    # (in `order`) and free columns. So a pivot col is UNDETERMINED (nonzero in some null
    # vector) iff its row touches a free col, transitively. Memoize over reverse order.
    freeset = set(free_cols)
    depends_free = {}
    for c in reversed(order):
        dep = False
        for k, v in pivots[c].items():
            if k == c or v % p == 0:
                continue
            if k in freeset or (k in pivots and depends_free.get(k, False)):
                dep = True
                break
        depends_free[c] = dep
    undetermined = set(free_cols) | {c for c in pivots if depends_free.get(c, False)}
    return rank, undetermined
