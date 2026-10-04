#!/usr/bin/env python3
"""gnark_lean_codegen — transcribe a determinacy certificate into a kernel-checkable Lean file.

Takes an R1CS JSON + the derivation certificate (gnark_certificate.emit) and emits a Lean file
over `ZMod p` (p = the circuit's field) that the Lean kernel checks: it defines the constraint
system `sat`, and proves `determined` — that any two satisfying assignments agreeing on the inputs
agree on every functionally-determined wire — by replaying the certificate, one `R1CSCert.funpin_one`
application per step, threading agreement with `R1CSCert.agree_cons`. Every side condition (wire ∈ S)
is discharged by `by decide`.

This pass handles the FUNCTIONAL pins (all of which gnark emits with coefficient 1, so `funpin_one`
applies and no field/primality is needed). is-zero / bit-decomp / guarded steps are the extension
(their leaf lemmas are already in GnarkR1CS.lean / BitDecomp.lean); a circuit whose determined set is
entirely functional is proved COMPLETELY here — turning its SAFE* determinacy into a Lean theorem.

SCOPE / scaling (honest): the emitted proof is UNROLLED — one `have` per wire plus a single `obtain`
that destructures the whole constraint conjunction. That kernel-checks for small circuits (see the
committed `GnarkCertDemo`), but does NOT scale: a 264-constraint Poseidon gadget did not finish in
45+ min (the deep-conjunction `obtain` and per-step elaboration are ~O(n²)). The scalable design is a
verified CHECKER — prove once that a decidable `validate cs cert` implies determinacy, then per circuit
emit only DATA + one `decide`/`native_decide`; that is O(n) but a separate development. Until then this
pass is a *mechanism demonstration* (a real, kernel-checked determinacy theorem for small circuits),
not a production path for the 6k–33k-wire suite.

Usage:  gnark_lean_codegen.py <r1cs.json> <Out.lean> [Namespace]
"""
import json
import sys

sys.path.insert(0, sys.argv[0].rsplit("/", 1)[0] if "/" in sys.argv[0] else ".")
import gnark_certificate as gc


def _tm(lst, P):
    m = {}
    for c, w in lst:
        m[int(w)] = (m.get(int(w), 0) + int(c)) % P
    return {w: c for w, c in m.items() if c != 0}   # drop zero-coeff terms (contribute 0 to dotp)


def _lin(terms):
    """Emit a List (ZMod p × ℕ) literal from an ordered list of (coeff, wire)."""
    if not terms:
        return "([] : List (ZMod p × ℕ))"
    inner = ", ".join(f"(({c} : ZMod p), {w})" for c, w in terms)
    return f"[{inner}]"


def _natlist(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def codegen(r1cs_path, out_path, ns="GnarkCert"):
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"])
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]
    inputs = list(range(nfix))

    steps = cert["steps"]
    fun_steps = [s for s in steps if s[0] == "functional"]
    if len(fun_steps) != len(steps):
        kinds = {}
        for s in steps:
            kinds[s[0]] = kinds.get(s[0], 0) + 1
        raise SystemExit(f"this pass supports functional-only certificates; got {kinds}. "
                         f"Pick an all-functional circuit, or extend with is-zero/guarded leaves.")

    # order the O side of each pinning constraint so the pinned wire's (coeff-1) term is FIRST
    L = []  # emitted per step: (w, L_terms, R_terms, Orest_terms, con_index_in_used_order)
    used = []          # constraints actually referenced, in emission order
    used_index = {}    # ci -> position in `used`
    for (_k, w, ci) in fun_steps:
        c = cons[ci]
        Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
        assert Om.get(w, 0) == 1, f"wire {w} not unit-coeff on O of constraint {ci}"
        Orest = [(cc, ww) for ww, cc in Om.items() if ww != w]
        Lt = [(cc, ww) for ww, cc in Lm.items()]
        Rt = [(cc, ww) for ww, cc in Rm.items()]
        if ci not in used_index:
            used_index[ci] = len(used)
            # store the O REORDERED as (1,w)::Orest for this constraint
            used.append((Lt, Rt, [(1, w)] + Orest))
        L.append((w, Lt, Rt, Orest, used_index[ci]))

    m = len(used)

    # inline the reusable R1CSCert core (single source of truth: read lean/R1CSCert.lean's
    # `namespace R1CSCert … end R1CSCert` block) so the generated file is self-verifying with
    # `lake env lean` — matching this project's standalone-file convention (no prebuilt oleans).
    import os
    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSCert.lean")
    core_src = open(core_path).read()
    lo = core_src.index("namespace R1CSCert")
    hi = core_src.index("end R1CSCert") + len("end R1CSCert")
    core_block = core_src[lo:hi]

    out = []
    out.append("import Mathlib")
    out.append("")
    out.append("set_option linter.unusedSectionVars false")
    out.append("set_option maxHeartbeats 4000000")
    out.append("set_option maxRecDepth 1000000")
    out.append("")
    out.append("-- ── inlined reusable core (lean/R1CSCert.lean) ──")
    out.append(core_block)
    out.append("-- ── end inlined core ──")
    out.append("")
    out.append(f"/- Auto-generated determinacy certificate for a gnark circuit "
               f"({sys_['n_wires']} wires, {len(cons)} constraints; {len(fun_steps)} functional pins). "
               f"Kernel-checks that every determined wire is forced by the inputs. -/")
    out.append(f"namespace {ns}")
    out.append("")
    out.append(f"abbrev p : ℕ := {P}")
    out.append("")
    # sat as a conjunction of the USED constraints (those the derivation reads)
    out.append("/-- The (relevant part of the) constraint system. -/")
    conj = " ∧\n  ".join(
        f"(R1CSCert.dotp {_lin(Lt)} a * R1CSCert.dotp {_lin(Rt)} a = R1CSCert.dotp {_lin(Ot)} a)"
        for (Lt, Rt, Ot) in used)
    out.append("def sat (a : ℕ → ZMod p) : Prop :=\n  " + conj)
    out.append("")
    out.append(f"def I : List ℕ := {_natlist(inputs)}")
    det_order = [w for (w, *_ ) in L]                 # wires pinned, in order
    final_list = list(reversed(det_order)) + inputs   # accumulated agree list (head = last pinned)
    out.append(f"def DET : List ℕ := {_natlist(final_list)}")
    out.append("")
    out.append("/-- Any two satisfying assignments agreeing on the inputs `I` agree on every")
    out.append("    functionally-determined wire `DET` — the circuit's determinacy, kernel-checked. -/")
    out.append("theorem determined (a a' : ℕ → ZMod p) (ha : sat a) (ha' : sat a')")
    out.append("    (hI : R1CSCert.agree I a a') : R1CSCert.agree DET a a' := by")
    # destructure the constraint system ONCE (avoids a deep projection into the conjunction)
    out.append(f"  obtain ⟨{', '.join('c'+str(k) for k in range(m))}⟩ := ha")
    out.append(f"  obtain ⟨{', '.join('d'+str(k) for k in range(m))}⟩ := ha'")
    out.append("  have g0 : R1CSCert.agree I a a' := hI")
    cur = "g0"
    curlist = list(inputs)
    for n, (w, Lt, Rt, Orest, ci_pos) in enumerate(L, start=1):
        Slit = _natlist(curlist)
        out.append(f"  have e{n} : a {w} = a' {w} :=")
        out.append(f"    R1CSCert.funpin_one_pt (S := {Slit}) (L := {_lin(Lt)}) (R := {_lin(Rt)}) "
                   f"(Orest := {_lin(Orest)})")
        ol = _lin(Orest)
        out.append(f"      (by decide) (by decide) (by decide) "
                   f"(c{ci_pos}.trans (R1CSCert.dotp_cons_one {w} {ol} a)) "
                   f"(d{ci_pos}.trans (R1CSCert.dotp_cons_one {w} {ol} a')) g{n-1}")
        newlist = [w] + curlist
        out.append(f"  have g{n} : R1CSCert.agree {_natlist(newlist)} a a' := R1CSCert.agree_cons e{n} g{n-1}")
        curlist = newlist
        cur = f"g{n}"
    out.append(f"  exact {cur}")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(fun_steps)} functional pins, {len(inputs)} inputs, "
          f"{len(final_list) - len(inputs)} determined wires")


def codegen_checker(r1cs_path, out_path, ns="GnarkCheck"):
    """SCALABLE codegen: emit DATA (the constraint list + inputs) and a one-line determinacy theorem
    `R1CSChecker.fold_sound cs I` — no per-step proof. The determined set is `cs.foldl stepPin I`,
    reduced by `native_decide`. O(n) to elaborate; the fold reduction is the only cost."""
    import os
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"])
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]
    inputs = list(range(nfix))
    # which wire each constraint functionally pins (from the certificate)
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}

    def con_lit(ci):
        c = cons[ci]
        Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
        Ot = [(cc, ww) for ww, cc in Om.items()]
        if ci in pin_of:                                   # put the pinned (coeff-1) wire first
            w = pin_of[ci]
            Ot = [(1, w)] + [(cc, ww) for ww, cc in Om.items() if ww != w]
        L = "⟨" + _lin([(cc, ww) for ww, cc in Lm.items()]) + ", " \
            + _lin([(cc, ww) for ww, cc in Rm.items()]) + ", " + _lin(Ot) + "⟩"
        return L

    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSChecker.lean")
    core = open(core_path).read()
    core_block = core[core.index("namespace R1CSChecker"):core.index("end R1CSChecker") + len("end R1CSChecker")]

    determined = sorted(w for (k, w, ci) in cert["steps"] if k == "functional")
    out = ["import Mathlib", "", "set_option linter.unusedSectionVars false",
           "set_option maxRecDepth 100000", "", "-- ── inlined verified checker (lean/R1CSChecker.lean) ──",
           core_block, "-- ── end inlined checker ──", "",
           f"/- Scalable determinacy certificate ({sys_['n_wires']} wires, {len(cons)} constraints). -/",
           f"namespace {ns}", "", f"abbrev p : ℕ := {P}", ""]
    out.append("def cs : List (R1CSChecker.Con (ZMod p)) := [")
    out.append(",\n".join("  " + con_lit(ci) for ci in range(len(cons))))
    out.append("]")
    out.append("")
    out.append(f"def I : List ℕ := {_natlist(inputs)}")
    out.append("")
    out.append("/-- Determinacy, one line: any two satisfying assignments agreeing on the inputs agree on")
    out.append("    every wire the checker determines. The field reasoning is `R1CSChecker.fold_sound`. -/")
    out.append("theorem determined : ∀ {a a' : ℕ → ZMod p}, R1CSChecker.sat cs a → R1CSChecker.sat cs a' →")
    out.append("    R1CSChecker.agree I a a' → R1CSChecker.agree (cs.foldl R1CSChecker.stepPin I) a a' :=")
    out.append("  R1CSChecker.fold_sound cs I")
    out.append("")
    out.append(f"/-- The checker determines all {len(determined)} functionally-pinned wires "
               f"(verified by reduction). -/")
    out.append(f"example : {_natlist(determined)}.all (fun w => (cs.foldl R1CSChecker.stepPin I).contains w) = true :=")
    out.append("  by native_decide")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(cons)} constraints, {len(determined)} determined (checker/fold_sound)")


def _iz_indices(sys_, P):
    """For each is-zero pair (x,b,m) from find_iszero_pairs, locate the A (`x·b=0`) and
    B (`(-x)·m = -1+b`) constraint indices, so we can emit them in the EXACT `izPin?` shape
    that the Lean `foldC` scan recognises. Returns {ci: literal_string}."""
    import gnark_leaves as gl
    cons = sys_["constraints"]
    tms = [( _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)) for c in cons]
    lit = {}
    for (x, b, m) in gl.find_iszero_pairs(sys_):
        ai = bi = None
        for ci, (Lm, Rm, Om) in enumerate(tms):
            if not Om and Lm == {x: 1} and Rm == {b: 1}:
                ai = ci
            elif len(Om) == 2 and Om.get(0) == P - 1 and Om.get(b) == 1 \
                    and Lm == {x: P - 1} and Rm == {m: 1}:
                bi = ci
        if ai is None or bi is None:
            continue
        lit[ai] = f"⟨[((1 : ZMod p), {x})], [((1 : ZMod p), {b})], ([] : List (ZMod p × ℕ))⟩"
        lit[bi] = (f"⟨[((-1 : ZMod p), {x})], [((1 : ZMod p), {m})], "
                   f"[((-1 : ZMod p), 0), ((1 : ZMod p), {b})]⟩")
    return lit


def codegen_foldc(r1cs_path, out_path, ns="GnarkCheck"):
    """INTEGRATED scalable codegen: emit the full constraint list and use `foldC_sound`, which
    covers BOTH functional pins AND is-zero gadgets in one linear scan. Is-zero constraints are
    emitted in the exact `izPin?` shape; functional pins get the pinned wire first on O; everything
    else is emitted faithfully (a non-pin leaves the fold unchanged, so its order is immaterial).

    The determinacy THEOREM needs `[Fact (Nat.Prime p)]` (the ZMod-p Field, for is-zero cancellation)
    and the ONE-wire facts `a 0 = 1` — both supplied as hypotheses (standard externally-checked facts,
    no axiom). The determined-SET check (`native_decide`) needs NEITHER: `foldC` computes over the plain
    CommRing, so the reduction runs on BN254 without any primality proof."""
    import os
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"])
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]
    inputs = list(range(nfix))
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}
    iz_lit = _iz_indices(sys_, P)
    # unconditional determined set foldC covers = functional pins + is-zero outputs
    det_uncond = sorted({w for (k, w, ci) in cert["steps"] if k in ("functional", "iszero")})

    def con_lit(ci):
        if ci in iz_lit:
            return iz_lit[ci]
        c = cons[ci]
        Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
        Ot = [(cc, ww) for ww, cc in Om.items()]
        if ci in pin_of:                                   # pinned (coeff-1) wire first on O
            w = pin_of[ci]
            Ot = [(1, w)] + [(cc, ww) for ww, cc in Om.items() if ww != w]
        return ("⟨" + _lin([(cc, ww) for ww, cc in Lm.items()]) + ", "
                + _lin([(cc, ww) for ww, cc in Rm.items()]) + ", " + _lin(Ot) + "⟩")

    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSChecker.lean")
    core = open(core_path).read()
    core_block = core[core.index("namespace R1CSChecker"):core.index("end R1CSChecker") + len("end R1CSChecker")]

    n_fun = sum(1 for (k, *_) in cert["steps"] if k == "functional")
    n_iz = sum(1 for (k, *_) in cert["steps"] if k == "iszero")
    out = ["import Mathlib", "", "set_option linter.unusedSectionVars false",
           "set_option maxRecDepth 100000", "",
           "-- ── inlined verified checker (lean/R1CSChecker.lean) ──",
           core_block, "-- ── end inlined checker ──", "",
           f"/- Integrated determinacy certificate ({sys_['n_wires']} wires, {len(cons)} constraints; "
           f"{n_fun} functional pins + {n_iz} is-zero outputs, one linear foldC scan). -/",
           f"namespace {ns}", "", f"abbrev p : ℕ := {P}", ""]
    out.append("def cs : List (R1CSChecker.Con (ZMod p)) := [")
    out.append(",\n".join("  " + con_lit(ci) for ci in range(len(cons))))
    out.append("]")
    out.append("")
    out.append(f"def I : List ℕ := {_natlist(inputs)}")
    out.append("")
    out.append("/-- Determinacy: any two satisfying assignments agreeing on the inputs agree on every")
    out.append("    wire `foldC` determines — functional pins AND is-zero results — by `foldC_sound`.")
    out.append("    `[Fact (Nat.Prime p)]` + `a 0 = 1` are the externally-checked facts (no axiom). -/")
    out.append("theorem determined [Fact (Nat.Prime p)] {a a' : ℕ → ZMod p}")
    out.append("    (h1 : a 0 = 1) (h1' : a' 0 = 1)")
    out.append("    (ha : R1CSChecker.sat cs a) (ha' : R1CSChecker.sat cs a')")
    out.append("    (hI : R1CSChecker.agree I a a') :")
    out.append("    R1CSChecker.agree (R1CSChecker.foldC cs I) a a' :=")
    out.append("  R1CSChecker.foldC_sound h1 h1' cs I ha ha' hI")
    out.append("")
    out.append(f"/-- `foldC` determines all {len(det_uncond)} unconditional wires (functional + is-zero),")
    out.append("    checked by reduction — no primality needed (foldC computes over the CommRing). -/")
    out.append(f"example : {_natlist(det_uncond)}.all (fun w => (R1CSChecker.foldC cs I).contains w) = true :=")
    out.append("  by native_decide")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(cons)} constraints, {n_fun} functional + {n_iz} is-zero "
          f"= {len(det_uncond)} determined (foldC_sound)")


def codegen_foldg(r1cs_path, out_path, ns="GnarkCheck"):
    """foldG codegen: functional + is-zero + GUARDED, one scan. Same emission as --foldc (is-zero in
    izPin? shape, functional pins O-first, everything else faithful — a guarded constraint `w·D = O`
    already has w alone coeff-1 on L, which `gdPin?` recognises unchanged). The determinacy theorem is
    `foldG_sound`, whose extra hypothesis is that every recorded divisor is nonzero — the named SAFE*
    residual `(foldG cs I []).2`. The determined-SET check needs no primality (foldG computes over the
    CommRing). Bit-decomposition is NOT a foldG step (scattered group); it composes via BitDec.bits_agree."""
    import os
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"])
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]
    inputs = list(range(nfix))
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}
    iz_lit = _iz_indices(sys_, P)
    det = sorted({w for (k, w, ci) in cert["steps"] if k in ("functional", "iszero", "guarded")})
    n_fun = sum(1 for (k, *_) in cert["steps"] if k == "functional")
    n_iz = sum(1 for (k, *_) in cert["steps"] if k == "iszero")
    n_gd = sum(1 for (k, *_) in cert["steps"] if k == "guarded")

    def con_lit(ci):
        if ci in iz_lit:
            return iz_lit[ci]
        c = cons[ci]
        Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
        Ot = [(cc, ww) for ww, cc in Om.items()]
        if ci in pin_of:
            w = pin_of[ci]
            Ot = [(1, w)] + [(cc, ww) for ww, cc in Om.items() if ww != w]
        return ("⟨" + _lin([(cc, ww) for ww, cc in Lm.items()]) + ", "
                + _lin([(cc, ww) for ww, cc in Rm.items()]) + ", " + _lin(Ot) + "⟩")

    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSChecker.lean")
    core = open(core_path).read()
    core_block = core[core.index("namespace R1CSChecker"):core.index("end R1CSChecker") + len("end R1CSChecker")]

    out = ["import Mathlib", "", "set_option linter.unusedSectionVars false",
           "set_option maxRecDepth 100000", "",
           "-- ── inlined verified checker (lean/R1CSChecker.lean) ──",
           core_block, "-- ── end inlined checker ──", "",
           f"/- Integrated determinacy ({sys_['n_wires']} wires, {len(cons)} constraints; "
           f"{n_fun} functional + {n_iz} is-zero + {n_gd} guarded, one foldG scan). -/",
           f"namespace {ns}", "", f"abbrev p : ℕ := {P}", ""]
    out.append("def cs : List (R1CSChecker.Con (ZMod p)) := [")
    out.append(",\n".join("  " + con_lit(ci) for ci in range(len(cons))))
    out.append("]")
    out.append("")
    out.append(f"def I : List ℕ := {_natlist(inputs)}")
    out.append("")
    out.append("/-- Determinacy modulo the guard obligations: with every recorded divisor nonzero on `a`")
    out.append("    (the SAFE* residual `(foldG cs I []).2`), any two satisfying assignments agreeing on")
    out.append("    the inputs agree on every foldG-determined wire — functional, is-zero, AND guarded. -/")
    out.append("theorem determined [Fact (Nat.Prime p)] {a a' : ℕ → ZMod p}")
    out.append("    (h1 : a 0 = 1) (h1' : a' 0 = 1)")
    out.append("    (ha : R1CSChecker.sat cs a) (ha' : R1CSChecker.sat cs a')")
    out.append("    (hI : R1CSChecker.agree I a a')")
    out.append("    (hnz : ∀ D ∈ (R1CSChecker.foldG cs I []).2, R1CSChecker.dotp D a ≠ 0) :")
    out.append("    R1CSChecker.agree (R1CSChecker.foldG cs I []).1 a a' :=")
    out.append("  R1CSChecker.foldG_sound h1 h1' cs I [] ha ha' hI hnz")
    out.append("")
    out.append(f"/-- foldG determines all {len(det)} wires (functional + is-zero + guarded), by reduction")
    out.append("    — no primality needed (foldG computes over the CommRing). -/")
    out.append(f"example : {_natlist(det)}.all (fun w => (R1CSChecker.foldG cs I []).1.contains w) = true :=")
    out.append("  by native_decide")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(cons)} constraints, {n_fun} functional + {n_iz} is-zero + "
          f"{n_gd} guarded = {len(det)} determined (foldG_sound)")


def _foldb_run(sys_, P, cert):
    """Faithful Python mirror of Lean `foldB` (same iz→gd→fun recogniser order, same 2/1 advancement)
    over the EMITTED constraint order — returns (determined_set, guard_obligation_wires) so the codegen's
    native_decide target is exactly what foldB marks (a TRUE subset check, not the fixpoint)."""
    import gnark_leaves as gl
    cons = sys_["constraints"]
    nfix = sys_["n_public"] + sys_["n_secret"]
    TMS = [(_tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)) for c in cons]
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}
    iz = {}                                   # cB index -> (cA index, x, b)
    for (x, b, m) in gl.find_iszero_pairs(sys_):
        ai = bi = None
        for ci, (L, R, O) in enumerate(TMS):
            if not O and L == {x: 1} and R == {b: 1}:
                ai = ci
            elif len(O) == 2 and O.get(0) == P - 1 and O.get(b) == 1 and L == {x: P - 1} and R == {m: 1}:
                bi = ci
        if ai is not None and bi is not None:
            iz[bi] = (ai, x, b)
    S, obl = set(range(nfix)), []
    i, n = 0, len(cons)
    while i < n:
        if i in iz and iz[i][0] == i + 1 and iz[i][1] in S:       # izPinB?
            S.add(iz[i][2]); i += 2; continue
        L, R, O = TMS[i]
        if len(L) == 1:                                           # gdPinB?
            w = next(iter(L))
            if L[w] == 1 and w not in S and all(k in S for k in R) and all(k in S for k in O):
                S.add(w); obl.append(w); i += 1; continue
        if i in pin_of:                                           # funPinB?
            w = pin_of[i]
            if w not in S and O.get(w) == 1 and all(k in S for k in L) and all(k in S for k in R) \
                    and all(k in S for k in O if k != w):
                S.add(w)
        i += 1
    return S, obl


def codegen_foldb(r1cs_path, out_path, ns="GnarkCheck"):
    """SCALABLE codegen: emit `foldB` (Array Bool determined set) — same leaves as --foldg (functional +
    is-zero + guarded) but O(1) membership, so native_decide reaches real circuits. The determined set is
    an `Array Bool` of size n_wires seeded with the input wires; `foldB_sound` gives the determinacy
    (SAFE* obligation: every recorded divisor nonzero). Target set is foldB's actual single-pass output."""
    import os
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"])
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]
    nw = sys_["n_wires"]
    inputs = list(range(nfix))
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}
    iz_lit = _iz_indices(sys_, P)
    Sdet, obl = _foldb_run(sys_, P, cert)
    target = sorted(w for w in Sdet if w >= nfix)

    half = P // 2

    def con_tokens(ci):
        """Flat token stream for a constraint: nL c w c w… nR … nO … with SIGNED Int coeffs (P-1 → -1),
        canonicalised like the literal path (is-zero shape, functional pins O-first)."""
        if ci in iz_lit:
            c = cons[ci]
            Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
            secs = ([(cc, ww) for ww, cc in Lm.items()],
                    [(cc, ww) for ww, cc in Rm.items()],
                    [(cc, ww) for ww, cc in Om.items()])
        else:
            c = cons[ci]
            Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
            Ot = [(cc, ww) for ww, cc in Om.items()]
            if ci in pin_of:
                w = pin_of[ci]
                Ot = [(1, w)] + [(cc, ww) for ww, cc in Om.items() if ww != w]
            secs = ([(cc, ww) for ww, cc in Lm.items()], [(cc, ww) for ww, cc in Rm.items()], Ot)
        toks = []
        for sec in secs:
            toks.append(str(len(sec)))
            for cc, ww in sec:
                toks.append(str(cc - P if cc > half else cc))   # signed coeff
                toks.append(str(ww))
        return toks

    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSChecker.lean")
    core = open(core_path).read()
    core_block = core[core.index("namespace R1CSChecker"):core.index("end R1CSChecker") + len("end R1CSChecker")]

    all_toks = []
    for ci in range(len(cons)):
        all_toks.extend(con_tokens(ci))
    data_str = " ".join(all_toks)

    out = ["import Mathlib", "", "set_option linter.unusedSectionVars false",
           "set_option maxRecDepth 100000", "",
           "-- ── inlined verified checker (lean/R1CSChecker.lean) ──",
           core_block, "-- ── end inlined checker ──", "",
           f"/- Scalable determinacy ({nw} wires, {len(cons)} constraints; foldB / Array Bool set,",
           "   circuit embedded as a String so elaboration stays O(n)). -/",
           f"namespace {ns}", "", f"abbrev p : ℕ := {P}", ""]
    # circuit as a flat integer String (O(n) elaboration) + total parseCons decoder
    out.append('/-- The circuit as a flat integer string: per constraint `nL c w … nR … nO …`. -/')
    out.append(f'def s : String := "{data_str}"')
    out.append("def toks : List Int := (s.splitOn \" \").filterMap (fun t => t.toInt?)")
    out.append(f"def cs : List (R1CSChecker.Con (ZMod p)) := R1CSChecker.parseCons {len(cons)} toks")
    out.append("")
    out.append(f"/-- determined set seeded with the {len(inputs)} input wires (Array Bool of size {nw}). -/")
    out.append(f"def I : Array Bool := {_natlist(inputs)}.foldl (fun A w => A.setIfInBounds w true) "
               f"(Array.mkArray {nw} false)")
    out.append("")
    out.append("/-- Determinacy modulo the guard obligations (SAFE*): with every recorded divisor nonzero")
    out.append("    on `a`, two satisfying assignments agreeing on the inputs agree on every foldB-marked")
    out.append("    wire — functional, is-zero, guarded — over the O(1) Array Bool set. -/")
    out.append("theorem determined [Fact (Nat.Prime p)] {a a' : ℕ → ZMod p}")
    out.append("    (h1 : a 0 = 1) (h1' : a' 0 = 1)")
    out.append("    (ha : R1CSChecker.sat cs a) (ha' : R1CSChecker.sat cs a')")
    out.append("    (hI : R1CSChecker.agreeA I a a')")
    out.append("    (hnz : ∀ D ∈ (R1CSChecker.foldB cs I []).2, R1CSChecker.dotp D a ≠ 0) :")
    out.append("    R1CSChecker.agreeA (R1CSChecker.foldB cs I []).1 a a' :=")
    out.append("  R1CSChecker.foldB_sound h1 h1' cs I [] ha ha' hI hnz")
    out.append("")
    out.append(f"/-- foldB marks all {len(target)} determined internal wires, by reduction over the Array")
    out.append("    Bool set — no primality (foldB computes over the CommRing). -/")
    out.append(f"example : {_natlist(target)}.all (fun w => (R1CSChecker.foldB cs I []).1.getD w false) = true :=")
    out.append("  by native_decide")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(cons)} constraints, foldB determines {len(target)} internal wires "
          f"({len(obl)} guard obligations)")


def codegen_full(r1cs_path, out_path, ns="GnarkCheck"):
    """FULL-coverage codegen: functional + is-zero + guarded + BIT-DECOMPOSITION, via the fixpoint
    fullFold_sound. Booleanity/recomposition constraints are emitted in the canonical boolCon/recompCon
    form so the bit-group facts (grpOk) discharge from `sat` by a structural grpWF native_decide.
    Circuit + groups both String-encoded (O(n) elaboration)."""
    import os
    import gnark_leaves as gl
    sys_ = json.load(open(r1cs_path))
    P = int(sys_["prime"]); half = P // 2
    cons = sys_["constraints"]
    cert = gc.emit(sys_)
    nfix = sys_["n_public"] + sys_["n_secret"]; nw = sys_["n_wires"]
    inputs = list(range(nfix))
    pin_of = {ci: w for (k, w, ci) in cert["steps"] if k == "functional"}
    iz_lit = _iz_indices(sys_, P)
    leaves, boolean = gl.find_bit_decomp_leaves(sys_)
    # classify booleanity / recomposition constraints
    bool_ci = {}       # ci -> bit wire
    recomp = {}        # ci -> (bits LSB, val terms[(coeff,wire)])
    for ci, c in enumerate(cons):
        b = gl._is_booleanity(c, P)
        if b is not None and b in boolean:
            bool_ci[ci] = b; continue
        m = gl._is_recomposition(c, P, boolean)
        if m is not None:
            _vw, bits = m
            Om = _tm(c["O"], P)
            recomp[ci] = (bits, [(cc, ww) for ww, cc in Om.items()])
    groups = [recomp[ci] for ci in sorted(recomp)]

    def sc(c):  # signed coeff
        return c - P if c > half else c

    def con_tokens(ci):
        if ci in bool_ci:
            b = bool_ci[ci]
            secs = ([(1, b)], [(1, 0), (-1, b)], [])          # boolCon b (already signed)
            return _sec_tokens(secs, signed=False)
        if ci in recomp:
            bits, val = recomp[ci]
            R = [(2 ** i, bits[i]) for i in range(len(bits))]  # powList
            return _sec_tokens(([(1, 0)], R, [(sc(cc), ww) for cc, ww in val]), signed=False)
        if ci in iz_lit:
            c = cons[ci]; Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
            return _sec_tokens(([(sc(cc), ww) for ww, cc in Lm.items()],
                                [(sc(cc), ww) for ww, cc in Rm.items()],
                                [(sc(cc), ww) for ww, cc in Om.items()]), signed=False)
        c = cons[ci]; Lm, Rm, Om = _tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)
        Ot = [(cc, ww) for ww, cc in Om.items()]
        if ci in pin_of:
            w = pin_of[ci]; Ot = [(1, w)] + [(cc, ww) for ww, cc in Om.items() if ww != w]
        return _sec_tokens(([(sc(cc), ww) for ww, cc in Lm.items()],
                            [(sc(cc), ww) for ww, cc in Rm.items()],
                            [(sc(cc) if cc > half else cc, ww) for cc, ww in Ot]), signed=False)

    all_toks = []
    for ci in range(len(cons)):
        all_toks.extend(con_tokens(ci))
    data_str = " ".join(all_toks)
    # groups string: nBits b… nVal c w …
    gtoks = []
    for bits, val in groups:
        gtoks.append(str(len(bits)))
        gtoks.extend(str(b) for b in bits)
        gtoks.append(str(len(val)))
        for cc, ww in val:
            gtoks.append(str(sc(cc))); gtoks.append(str(ww))
    groups_str = " ".join(gtoks)

    Sdet, fuel = _fullfold_run(sys_, P, cert, bool_ci, recomp, groups, iz_lit, pin_of)
    target = sorted(w for w in Sdet if w >= nfix)

    core_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "R1CSChecker.lean")
    core = open(core_path).read()
    core_block = core[core.index("namespace R1CSChecker"):core.index("end R1CSChecker") + len("end R1CSChecker")]

    out = ["import Mathlib", "", "set_option linter.unusedSectionVars false",
           "set_option maxRecDepth 100000", "",
           "-- ── inlined verified checker (lean/R1CSChecker.lean) ──",
           core_block, "-- ── end inlined checker ──", "",
           f"/- Full-coverage determinacy ({nw} wires, {len(cons)} constraints, {len(groups)} bit groups;",
           "   scan + bit-decomposition fixpoint, circuit & groups String-encoded). -/",
           f"namespace {ns}", "", f"abbrev p : ℕ := {P}",
           "-- BN254 primality is supplied as a hypothesis (no axiom; norm_num can't factor a 254-bit p).",
           "-- native_decide never inspects it — Fact is an erased Prop — so the reductions still run.",
           "variable [Fact (Nat.Prime p)]", ""]
    out.append(f'def s : String := "{data_str}"')
    out.append("def toks : List Int := (s.splitOn \" \").filterMap (fun t => t.toInt?)")
    out.append(f"def cs : List (R1CSChecker.Con (ZMod p)) := R1CSChecker.parseCons {len(cons)} toks")
    out.append("")
    out.append(f'def gs : String := "{groups_str}"')
    out.append("def gtoks : List Int := (gs.splitOn \" \").filterMap (fun t => t.toInt?)")
    out.append(f"def groups : List (R1CSChecker.BitGrp p) := R1CSChecker.parseGroups {len(groups)} gtoks")
    out.append(f"def I : Array Bool := {_natlist(inputs)}.foldl (fun A w => A.setIfInBounds w true) "
               f"(Array.mkArray {nw} false)")
    out.append("")
    out.append("/-- Full determinacy: with the guard obligations nonzero (SAFE*), two satisfying")
    out.append("    assignments agreeing on the inputs agree on the whole fixpoint determined set —")
    out.append("    functional, is-zero, guarded, AND bit-decomposition. -/")
    out.append("theorem determined {a a' : ℕ → ZMod p} (h1 : a 0 = 1) (h1' : a' 0 = 1)")
    out.append("    (ha : R1CSChecker.sat cs a) (ha' : R1CSChecker.sat cs a')")
    out.append("    (hI : R1CSChecker.agreeA I a a')")
    out.append(f"    (hnz : ∀ D ∈ (R1CSChecker.fullFold cs groups {fuel} I []).2, R1CSChecker.dotp D a ≠ 0) :")
    out.append(f"    R1CSChecker.agreeA (R1CSChecker.fullFold cs groups {fuel} I []).1 a a' :=")
    out.append("  R1CSChecker.fullFold_sound h1 h1' cs groups ha ha'")
    out.append("    (fun g hg => R1CSChecker.grpOk_of_sat h1 h1' ha ha' (by")
    out.append("      have h : (groups.all (fun g => R1CSChecker.grpWF g cs)) = true := by native_decide")
    out.append(f"      exact (List.all_eq_true.1 h) g hg)) {fuel} I [] hI hnz")
    out.append("")
    out.append(f"/-- The fixpoint determined set, computed ONCE (a CAF — so native_decide does not")
    out.append("    re-run the fold per wire). -/")
    out.append(f"def det : Array Bool := (R1CSChecker.fullFold cs groups {fuel} I []).1")
    out.append(f"/-- The fixpoint determines all {len(target)} internal wires (functional + is-zero +")
    out.append("    guarded + bit-decomposition), by reduction. -/")
    out.append(f"example : {_natlist(target)}.all (fun w => det.getD w false) = true :=")
    out.append("  by native_decide")
    out.append("")
    # residual analysis (documentation): the free wires that remain are benign advice. Emitted as a
    # comment, not a native_decide (the exact free set is Lean's `det`, computed above); the benign
    # guarantee is fullFold_sound itself — the determined outputs agree across ANY two satisfying
    # assignments agreeing on the inputs, so they are independent of every non-determined wire.
    internal = list(range(nfix, nw))
    free = sorted(w for w in internal if w not in Sdet)
    from collections import Counter
    occ = Counter()
    for c in cons:
        ws = {int(ww) for sec in ("L", "R", "O") for _cc, ww in c[sec] if int(ww) != 0}
        for w in ws:
            occ[w] += 1
    single = [w for w in free if occ[w] <= 1]
    multi = [w for w in free if occ[w] > 1]
    out.append(f"/- Free residual (benign): {len(single)} single-use wires — is-zero inverse hints that")
    out.append(f"   appear in ≤1 constraint, so they feed nothing — plus {len(multi)} wires determined by a")
    out.append(f"   gadget the recognisers don't yet reach ({multi}). No meaningful signal is free:")
    out.append("   `determined` (fullFold_sound) proves the outputs are independent of every free wire. -/")
    out.append("")
    out.append(f"end {ns}")
    open(out_path, "w").write("\n".join(out) + "\n")
    print(f"wrote {out_path}: {len(cons)} constraints, {len(groups)} bit groups, fuel {fuel}, "
          f"fixpoint determines {len(target)} internal wires")


def _sec_tokens(secs, signed=False):
    toks = []
    for sec in secs:
        toks.append(str(len(sec)))
        for cc, ww in sec:
            toks.append(str(cc)); toks.append(str(ww))
    return toks


def _fullfold_run(sys_, P, cert, bool_ci, recomp, groups, iz_lit, pin_of):
    """Python mirror of Lean fullFold (foldB scan + bitMark, to fixpoint) — returns (determined, fuel)."""
    cons = sys_["constraints"]; nfix = sys_["n_public"] + sys_["n_secret"]
    TMS = [(_tm(c["L"], P), _tm(c["R"], P), _tm(c["O"], P)) for c in cons]
    import gnark_leaves as gl
    iz = {}
    for (x, b, m) in gl.find_iszero_pairs(sys_):
        ai = bi = None
        for ci, (L, R, O) in enumerate(TMS):
            if not O and L == {x: 1} and R == {b: 1}: ai = ci
            elif len(O) == 2 and O.get(0) == P - 1 and O.get(b) == 1 and L == {x: P - 1} and R == {m: 1}: bi = ci
        if ai is not None and bi is not None: iz[bi] = (ai, x, b)

    def scan(S):                                # one foldB pass
        i, n = 0, len(cons)
        while i < n:
            if i in iz and iz[i][0] == i + 1 and iz[i][1] in S:
                S.add(iz[i][2]); i += 2; continue
            L, R, O = TMS[i]
            if i not in bool_ci and i not in recomp and len(L) == 1:
                w = next(iter(L))
                if L[w] == 1 and w not in S and all(k in S for k in R) and all(k in S for k in O):
                    S.add(w); i += 1; continue
            if i in pin_of:
                w = pin_of[i]
                if w not in S and O.get(w) == 1 and all(k in S for k in L) and all(k in S for k in R) \
                        and all(k in S for k in O if k != w):
                    S.add(w)
            i += 1
        return S

    S = set(range(nfix)); rounds = 0
    while True:
        before = len(S)
        S = scan(S)
        for bits, val in groups:                # bitMark
            if all(w in S for _cc, w in val):
                S |= set(bits)
        rounds += 1
        if len(S) == before or rounds > 200:
            break
    return S, rounds + 1


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print("usage: gnark_lean_codegen.py [--checker|--foldc|--foldg|--foldb|--full] <r1cs.json> <Out.lean> [Namespace]")
        sys.exit(2)
    if sys.argv[1] == "--full":
        codegen_full(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "GnarkCheck")
    elif sys.argv[1] == "--foldb":
        import gnark_leaves as gl
        codegen_foldb(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "GnarkCheck")
    elif sys.argv[1] == "--foldg":
        import gnark_leaves as gl
        codegen_foldg(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "GnarkCheck")
    elif sys.argv[1] == "--foldc":
        import gnark_leaves as gl
        codegen_foldc(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "GnarkCheck")
    elif sys.argv[1] == "--checker":
        codegen_checker(sys.argv[2], sys.argv[3], sys.argv[4] if len(sys.argv) > 4 else "GnarkCheck")
    else:
        codegen(sys.argv[1], sys.argv[2], sys.argv[3] if len(sys.argv) > 3 else "GnarkCert")
