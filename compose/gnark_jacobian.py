#!/usr/bin/env python3
"""gnark_jacobian — RESEARCH SPIKE: determinacy via the Jacobian / algebraic-matroid criterion.

Recasts under-constraint as computational algebraic geometry. On the solution variety
V(𝓘) of an R1CS ideal, a wire x_o is *determined* by the inputs x_I iff x_o lies in the
algebraic closure of x_I — an algebraic-matroid closure. The Jacobian criterion tests it by
LINEAR ALGEBRA at a satisfying witness p (exact here: char p ≈ 2^254 ≫ degree 2):

    tangent space  T = ker J(p)            (J = Jacobian of the constraints at p)
    fix the inputs (rows e_i, i∈I) :  M = [J(p); e_i]
    x_o is (first-order) determined by x_I  ⟺  x_o = 0 on ker(M)
    the FREE wires (nonzero somewhere in ker M) are the under-determined ones.

This sidesteps every wall the SMT/leaf approach hit: it is a rank/nullspace computation
(no finite-field SMT wall), it treats guards/selects/masks as ordinary polynomials (NO
case-splitting — the thing that defeated the syntactic F-2 analysis), and the witness point
comes free from the prover's solver.

HONEST SCOPE / open problem: the Jacobian decides ALGEBRAIC (in)dependence = transcendence
degree, i.e. "is the fiber positive-dimensional (a wire with a continuum of free values)".
  * full-rank in x_o  ⇒  x_o INFINITELY free given inputs  ⇒  a real under-constraint (SOUND).
  * rank-deficient    ⇒  x_o is a FINITELY-valued function of the inputs — but not necessarily
                         UNIQUE (e.g. w²=x pins w only up to sign). Finite-multiplicity
                         under-constraint (sign/root ambiguity) needs a secondary check.
So this is the sound detector for the dominant "free-witness" bug class; and, evaluated at a
branch-active witness, it captures the conditional (mask/select) freedom SMT could not scale to.
"""


def gf_nullspace(rows, ncols, p):
    """Basis of the null space of the matrix `rows` (list of {col:coef}) over GF(p).
    Returns (free_cols, basis) — free_cols = columns not pivoted (their coordinate can be
    nonzero in some null vector)."""
    # dense mod-p Gaussian elimination (fine for the prototype's small systems)
    M = [[0] * ncols for _ in rows]
    for i, r in enumerate(rows):
        for c, v in r.items():
            M[i][c] = v % p
    pivots = {}          # col -> row
    r = 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(M)) if M[i][c] % p != 0), None)
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][c], -1, p)
        M[r] = [(x * inv) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(a - f * b) % p for a, b in zip(M[i], M[r])]
        pivots[c] = r
        r += 1
        if r == len(M):
            break
    free_cols = [c for c in range(ncols) if c not in pivots]
    return free_cols, pivots, M


def jacobian_free_wires(constraints, witness, fixed, p, nwires):
    """Return the set of wires that are FIRST-ORDER FREE given `fixed` wires held constant,
    at the satisfying assignment `witness`. Empty free set (beyond the fixed) ⇒ every other
    wire is (first-order) determined by the fixed inputs.

    constraints: list of (L,R,O) term-maps {wire:coef} for (L·x)(R·x)=(O·x).
    witness: {wire: value}.  fixed: set of wire ids held constant (inputs, incl ONE=0)."""
    def dot(m):
        return sum(c * witness[w] for w, c in m.items()) % p
    rows = []
    for (L, R, O) in constraints:
        Lv, Rv = dot(L), dot(R)
        # ∂/∂x_k of (L·x)(R·x) − (O·x)  =  L_k·Rv + Lv·R_k − O_k
        row = {}
        for w, c in L.items():
            row[w] = (row.get(w, 0) + c * Rv) % p
        for w, c in R.items():
            row[w] = (row.get(w, 0) + Lv * c) % p
        for w, c in O.items():
            row[w] = (row.get(w, 0) - c) % p
        rows.append({w: v for w, v in row.items() if v % p != 0})
    for w in fixed:                      # fix inputs: e_w rows
        rows.append({w: 1})
    free_cols, pivots, M = gf_nullspace(rows, nwires, p)
    # A wire is UNDETERMINED iff its coordinate can be nonzero in some null vector:
    #   - every free column is (its own basis null vector has coord 1);
    #   - a pivot column whose RREF row has a nonzero entry in ANY free column depends on a
    #     free variable, so it too can be nonzero. (A pivot forced to 0 IS determined.)
    undet = set(free_cols)
    freeset = set(free_cols)
    for c, rr in pivots.items():
        if any(M[rr][f] % p != 0 for f in freeset):
            undet.add(c)
    return undet - set(fixed)

# ---------- exact F_p RREF backends -------------------------------------------
# The undetermined-wire logic needs a reduced row-echelon form of the Jacobian
# (+ fixed-input rows). Pure-Python gf_nullspace above is fine for the PoC's
# small systems; python-flint's fmpz_mod_mat.rref() is C-fast and is used for
# real circuits (hundreds–thousands of wires). Both return the SAME interface:
#   (pivots: {col->rref_row_index}, free_cols: [col], get: (row,col)->int).

def _rref_flint(rows, ncols, p):
    from flint import fmpz_mod_ctx, fmpz_mod_mat
    ctx = fmpz_mod_ctx(p)
    nr = len(rows)
    flat = [0] * (nr * ncols)
    for i, r in enumerate(rows):
        base = i * ncols
        for c, v in r.items():
            flat[base + c] = int(v) % p
    R, rank = fmpz_mod_mat(nr, ncols, flat, ctx).rref()
    # walk the RREF: pivot col of each row = its first nonzero entry
    def cell(i, j):
        return int(R[i, j])
    pivots, seen = {}, [False] * ncols
    for i in range(rank):
        for c in range(ncols):
            if cell(i, c) != 0:
                pivots[c] = i
                seen[c] = True
                break
    free_cols = [c for c in range(ncols) if not seen[c]]
    return pivots, free_cols, cell


def _rref_pure(rows, ncols, p):
    free_cols, pivots, M = gf_nullspace(rows, ncols, p)
    return pivots, free_cols, (lambda i, j: M[i][j] % p)


def _jacobian_rows(constraints, witness, fixed, p):
    """Build the Jacobian rows at `witness` plus the fixed-input indicator rows."""
    def dot(m):
        return sum(c * witness[w] for w, c in m.items()) % p
    rows = []
    for (L, R, O) in constraints:
        Lv, Rv = dot(L), dot(R)
        row = {}
        for w, c in L.items():
            row[w] = (row.get(w, 0) + c * Rv) % p
        for w, c in R.items():
            row[w] = (row.get(w, 0) + Lv * c) % p
        for w, c in O.items():
            row[w] = (row.get(w, 0) - c) % p
        rows.append({w: v for w, v in row.items() if v % p != 0})
    for w in fixed:
        rows.append({w: 1})
    return rows


def undetermined_wires(constraints, witness, fixed, p, nwires, backend="sparse"):
    """Wires that can be nonzero in some null vector of [J(witness); fix] — i.e.
    NOT determined by the fixed inputs. Default backend is sparse Gaussian
    elimination (gnark_sparse), which is exact and ~500x faster than the dense
    flint rref on real circuits (and the only one that reaches 21k+ wires);
    'flint'/'pure' select the dense RREF backends (kept for cross-checking)."""
    rows = _jacobian_rows(constraints, witness, fixed, p)
    if backend == "sparse":
        import gnark_sparse
        _, undet = gnark_sparse.sparse_support(rows, nwires, p)
        return undet - set(fixed)
    if backend == "pure":
        pivots, free_cols, get = _rref_pure(rows, nwires, p)
    else:
        try:
            pivots, free_cols, get = _rref_flint(rows, nwires, p)
        except ImportError:
            if backend == "flint":
                raise
            pivots, free_cols, get = _rref_pure(rows, nwires, p)
    freeset = set(free_cols)
    undet = set(free_cols)
    for c, rr in pivots.items():
        if any(get(rr, f) != 0 for f in freeset):
            undet.add(c)
    return undet - set(fixed)


# ---------- real-circuit driver: (R1CS JSON, witness JSON) --------------------

def _load_r1cs(path):
    import json
    d = json.load(open(path))
    p = int(d["prime"])
    def tm(lst):
        m = {}
        for coef, wid in lst:
            m[int(wid)] = (m.get(int(wid), 0) + int(coef)) % p
        return m
    cons = [(tm(c["L"]), tm(c["R"]), tm(c["O"])) for c in d["constraints"]]
    return d, p, cons


def _load_witness(path):
    import json
    d = json.load(open(path))
    return [int(v) for v in d["values"]]


def run_real(r1cs_path, wit_path, fix="inputs"):
    """Report the undetermined internal/advice wires of a real gnark circuit.
    fix='inputs' : hold public+secret DECLARED inputs constant (the advice model:
                   are all advice/internal wires determined by the inputs?).
    fix='public' : hold only public inputs (witness-uniqueness model)."""
    d, p, cons = _load_r1cs(r1cs_path)
    wv = _load_witness(wit_path)
    nwires = d["n_wires"]
    npub, nsec = d["n_public"], d["n_secret"]
    witness = {i: wv[i] for i in range(nwires)}
    nfix = npub if fix == "public" else npub + nsec
    fixed = set(range(nfix))  # wire 0..nfix-1 : ONE + public [+ secret]
    undet = undetermined_wires(cons, witness, fixed, p, nwires)
    advice = [w for w in range(nfix, nwires)]
    undet_adv = sorted(undet & set(advice))
    print(f"  wires={nwires} (pub={npub} sec={nsec} int={d['n_internal']}) "
          f"constraints={len(cons)}  fix={fix}({nfix})")
    if undet_adv:
        print(f"  UNDER-DETERMINED advice wires: {undet_adv}")
    else:
        print(f"  all {len(advice)} advice/internal wires DETERMINED by the inputs")
    return undet_adv


# ---------- proof-of-concept on the exact patterns that defeated SMT + the nonzero domain ----------
def _poc():
    P = 21888242871839275222246405745257275088548364400416034343698204186575808495617
    ONE = 0

    def show(name, constraints, witness, fixed, target, expect):
        free = jacobian_free_wires(constraints, witness, fixed | {ONE}, P, max(witness) + 1)
        verdict = "FREE (under-constrained)" if target in free else "determined (first-order)"
        print(f"  {name:34s} wire {target}: {verdict:28s}  [expected: {expect}]")

    print("Jacobian determinacy — proof of concept\n")

    # 1) bilinear  Y = X*W ;  inputs {Y}.  X should be FREE given Y (SMT: sat; here: free).
    #    wires: 0=ONE 1=Y 2=X 3=W
    show("bilinear  Y=X*W (fix Y)",
         [({2: 1}, {3: 1}, {1: 1})], {0: 1, 1: 6, 2: 2, 3: 3}, {1}, 2, "FREE")

    # 2) mask  x·(sel-1)=0 ;  the F-2 pattern.  Evaluate at the DANGEROUS branch sel=1:
    #    x is free; at sel=0 it is pinned. Jacobian at sel=1 must reveal the freedom.
    #    wires: 0=ONE 1=sel 2=x        constraint L={x}, R={sel, -1·ONE}, O={}
    mask = [({2: 1}, {1: 1, 0: P - 1}, {})]
    show("mask x·(sel-1)=0 @ sel=1 (fix sel)", mask, {0: 1, 1: 1, 2: 42}, {1}, 2, "FREE")
    show("mask x·(sel-1)=0 @ sel=0 (fix sel)", mask, {0: 1, 1: 0, 2: 0}, {1}, 2, "determined")

    # 3) sqrt  w*w = x ;  inputs {x}.  w is 2-valued (±) — honest LIMIT: Jacobian says
    #    'determined' (0-dim fiber) though w is not unique.  wires: 0=ONE 1=x 2=w
    show("sqrt w²=x (fix x)  [known limit]",
         [({2: 1}, {2: 1}, {1: 1})], {0: 1, 1: 9, 2: 3}, {1}, 2, "determined*")

    print("\n* the sqrt case exposes the finite-multiplicity gap: Jacobian tests transcendence")
    print("  (0-dim fiber), not uniqueness. A secondary check is needed for sign/root ambiguity.")


if __name__ == "__main__":
    import sys
    args = sys.argv[1:]
    if len(args) >= 2 and args[0].endswith(".json"):
        # real circuit:  gnark_jacobian.py <r1cs.json> <witness.json> [public|inputs]
        fix = args[2] if len(args) >= 3 else "inputs"
        run_real(args[0], args[1], fix=fix)
    else:
        _poc()
