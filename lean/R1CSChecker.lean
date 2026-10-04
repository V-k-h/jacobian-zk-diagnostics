import Mathlib

set_option linter.unusedSectionVars false

/-!
# A verified, O(n) R1CS determinacy checker

`R1CSCert` transcribes a certificate into an *unrolled* proof — one tactic step per wire — which does
not scale. This file is the scalable design: a single generic soundness theorem `fold_sound`, proved
once, whose per-circuit use is **only data plus one decidable evaluation**. The per-step check is
purely STRUCTURAL (is the pinned wire lone with coefficient 1 on the output side, are the other wires
already determined) — no field arithmetic — so the fold that computes the determined set reduces cheaply.

A circuit is `cs : List (Con F)`. `stepPin` walks the constraints in order, extending the determined-wire
list `S` whenever the next constraint functionally pins a new wire from wires already in `S` (the
straight-line / dependency order that gnark emits). `fold_sound` proves: any two satisfying assignments
agreeing on the inputs `I` agree on `cs.foldl stepPin I` — the whole determined set — with the field
reasoning discharged once by `funpin_one_pt`.

Leaf coverage: FUNCTIONAL pins go through `fold_sound` (single-pass, one constraint at a time). IS-ZERO
gadgets — which gnark emits as an ADJACENT constraint pair `cB : (-x)·m = -1+b`, `cA : x·b = 0`
(measured) — are handled by `foldC`, a scan that consumes either one constraint (functional) or two (an
is-zero pair), with soundness `foldC_sound`; so functional AND is-zero determinacy are both integrated
into one linear pass. The GUARDED leaf (`guarded_pin`, § Field) carries a `divisor≠0` obligation and is
proved but not yet folded in (its obligation is discharged separately by `Inertness.lean`). So `foldC`
now covers the whole UNCONDITIONAL determined set (functional + is-zero) of the deposit circuits.
-/

namespace R1CSChecker

variable {F : Type*} [CommRing F]

/-- Evaluate a sparse linear form `Σ cᵢ·a(wᵢ)`. -/
def dotp (l : List (F × ℕ)) (a : ℕ → F) : F := (l.map fun t => t.1 * a t.2).sum

@[simp] theorem dotp_nil (a : ℕ → F) : dotp ([] : List (F × ℕ)) a = 0 := rfl
@[simp] theorem dotp_cons (t : F × ℕ) (l : List (F × ℕ)) (a : ℕ → F) :
    dotp (t :: l) a = t.1 * a t.2 + dotp l a := rfl

/-- An R1CS constraint `(L·a)(R·a) = (O·a)`. -/
structure Con (F : Type*) where
  L : List (F × ℕ)
  R : List (F × ℕ)
  O : List (F × ℕ)
  deriving DecidableEq

def holds (c : Con F) (a : ℕ → F) : Prop := dotp c.L a * dotp c.R a = dotp c.O a

/-- The constraint system: every constraint holds. -/
def sat (cs : List (Con F)) (a : ℕ → F) : Prop := ∀ c ∈ cs, holds c a

def agree (S : List ℕ) (a a' : ℕ → F) : Prop := ∀ v ∈ S, a v = a' v

theorem dotp_agree {l : List (F × ℕ)} {S : List ℕ} {a a' : ℕ → F}
    (hl : ∀ t ∈ l, t.2 ∈ S) (h : agree S a a') : dotp l a = dotp l a' := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    have hts : ∀ x ∈ ts, x.2 ∈ S := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [dotp_cons, dotp_cons, ih hts, h t.2 (hl t (List.mem_cons_self t ts))]

theorem agree_cons {S : List ℕ} {w : ℕ} {a a' : ℕ → F}
    (hw : a w = a' w) (hS : agree S a a') : agree (w :: S) a a' := by
  intro v hv
  rcases List.mem_cons.1 hv with h | h
  · exact h ▸ hw
  · exact hS v h

/-- Functional pin, coefficient-1 point form (the field-algebra core, discharged once). -/
theorem funpin_one_pt {L R Orest : List (F × ℕ)} {w : ℕ} {S : List ℕ} {a a' : ℕ → F}
    (hL : ∀ t ∈ L, t.2 ∈ S) (hR : ∀ t ∈ R, t.2 ∈ S) (hO : ∀ t ∈ Orest, t.2 ∈ S)
    (hca : dotp L a * dotp R a = a w + dotp Orest a)
    (hca' : dotp L a' * dotp R a' = a' w + dotp Orest a')
    (hS : agree S a a') : a w = a' w := by
  rw [dotp_agree hL hS, dotp_agree hR hS, dotp_agree hO hS] at hca
  exact add_right_cancel (hca.symm.trans hca')

section Checker
variable [DecidableEq F]

/-- All wires of a linear form are already determined (∈ S). Decidable, purely structural. -/
def wiresIn (l : List (F × ℕ)) (S : List ℕ) : Bool := l.all (fun t => S.contains t.2)

theorem wiresIn_mem {l : List (F × ℕ)} {S : List ℕ} (h : wiresIn l S = true) :
    ∀ t ∈ l, t.2 ∈ S := by
  intro t ht
  have : S.contains t.2 = true := (List.all_eq_true.1 h) t ht
  simpa [List.contains_iff_mem] using this

/-- One pass step: if constraint `c`'s output side is `(1,w) :: Orest` with `w` new and `L,R,Orest`
already determined, add `w`; otherwise leave `S` unchanged. Purely structural — decidable. -/
def stepPin (S : List ℕ) (c : Con F) : List ℕ :=
  match c.O with
  | (t :: Orest) =>
      if t.1 = 1 ∧ wiresIn c.L S = true ∧ wiresIn c.R S = true ∧ wiresIn Orest S = true
      then t.2 :: S else S
  | [] => S

/-- **Per-step soundness.** If `c` holds on both assignments and they agree on `S`, they agree on
`stepPin S c`. The field work is exactly one `funpin_one_pt`. -/
theorem stepPin_agree (c : Con F) (S : List ℕ) {a a' : ℕ → F}
    (hc : holds c a) (hc' : holds c a') (hS : agree S a a') : agree (stepPin S c) a a' := by
  cases hO : c.O with
  | nil => simp only [stepPin, hO]; exact hS
  | cons t Orest =>
    simp only [stepPin, hO]
    by_cases hcond : t.1 = 1 ∧ wiresIn c.L S = true ∧ wiresIn c.R S = true ∧ wiresIn Orest S = true
    · rw [if_pos hcond]
      obtain ⟨h1, hLb, hRb, hOb⟩ := hcond
      refine agree_cons ?_ hS
      have pin : ∀ b : ℕ → F, holds c b → dotp c.L b * dotp c.R b = b t.2 + dotp Orest b := by
        intro b hb
        simp only [holds, hO, dotp_cons, h1, one_mul] at hb
        exact hb
      exact funpin_one_pt (wiresIn_mem hLb) (wiresIn_mem hRb) (wiresIn_mem hOb)
        (pin a hc) (pin a' hc') hS
    · rw [if_neg hcond]; exact hS

/-- **Fold soundness (the whole checker).** Two satisfying assignments agreeing on the inputs `I`
agree on `cs.foldl stepPin I` — the entire determined set the one-pass checker computes. Proved once;
a per-circuit determinacy theorem is then just `fold_sound` applied to concrete `cs`, `I`, with the
determined set obtained by reducing `cs.foldl stepPin I` (no per-step proof). -/
theorem fold_sound (cs : List (Con F)) : ∀ (I : List ℕ) {a a' : ℕ → F},
    sat cs a → sat cs a' → agree I a a' → agree (cs.foldl stepPin I) a a' := by
  induction cs with
  | nil => intro I a a' _ _ hI; simpa using hI
  | cons c cs' ih =>
    intro I a a' ha ha' hI
    have hc : holds c a := ha c (List.mem_cons_self c cs')
    have hc' : holds c a' := ha' c (List.mem_cons_self c cs')
    have hsat : sat cs' a := fun x hx => ha x (List.mem_cons_of_mem c hx)
    have hsat' : sat cs' a' := fun x hx => ha' x (List.mem_cons_of_mem c hx)
    have hstep : agree (stepPin I c) a a' := stepPin_agree c I hc hc' hI
    simpa [List.foldl] using ih (stepPin I c) hsat hsat' hstep

end Checker

/-!
## Field leaves (is-zero, guarded)

The is-zero and guarded pins need field cancellation / no-zero-divisors, hence a field base — for a
concrete circuit, `ZMod p` with `[Fact (Nat.Prime p)]` (a standard, externally-verified fact supplied
as a hypothesis; no axiom). These are the list-model analogues of `GnarkR1CS.r1cs_iszero` /
`r1cs_guarded`, in point form for a certificate replay.
-/
section Field
variable {F : Type*} [Field F]

/-- **is-zero leaf.** Given `x` determined (equal across the two runs) and the gadget constraints
`x·b = 0`, `x·m + b = 1` on both assignments, the result `b` is determined — unconditionally. The
inverse hint `m` may be free when `x = 0`, but is benign (it feeds only `x·m`, which is `0` there). -/
theorem iszero_pin {x b m : ℕ} {a a' : ℕ → F}
    (hx : a x = a' x)
    (h0 : a x * a b = 0) (h1 : a x * a m + a b = 1)
    (h0' : a' x * a' b = 0) (h1' : a' x * a' m + a' b = 1) : a b = a' b := by
  by_cases hz : a x = 0
  · have e1 : a b = 1 := by rw [hz, zero_mul, zero_add] at h1; exact h1
    have e2 : a' b = 1 := by rw [← hx, hz, zero_mul, zero_add] at h1'; exact h1'
    rw [e1, e2]
  · have e1 : a b = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hz
      · exact h
    have e2 : a' b = 0 := by
      rcases mul_eq_zero.mp h0' with h | h
      · rw [← hx] at h; exact absurd h hz
      · exact h
    rw [e1, e2]

/-- **Guarded pin.** If `w·d = num` on both runs with the divisor `d` determined and NONZERO (the
`SAFE*` side-condition) and `num` determined, then `w` is determined. Conditional on `d ≠ 0`; that
obligation is what the inertness argument (`Inertness.lean`) discharges for the padding-zero cases. -/
theorem guarded_pin {w : ℕ} {d num : F} {a a' : ℕ → F}
    (hd : d ≠ 0) (hca : a w * d = num) (hca' : a' w * d = num) : a w = a' w :=
  mul_right_cancel₀ hd (hca.trans hca'.symm)

end Field

/-!
## The integrated pass: functional pins AND is-zero gadgets, in one scan

gnark emits each is-zero gadget as an ADJACENT constraint pair — `cB : (-x)·m = -1 + b` immediately
followed by `cA : x·b = 0` (measured). So a single scan that consumes either one constraint (functional)
or two (an is-zero pair) covers both, keeping `sat` flat and the induction linear. `foldC` is that scan;
`foldC_sound` its soundness. The base field is needed for the is-zero cancellation.
-/
section Integrated
variable [DecidableEq F]   -- izPin?/foldC only need CommRing (from the namespace) + DecidableEq, so they
                            -- COMPUTE (native_decide) over any ZMod p without needing p prime.

/-- Recognise gnark's is-zero pair `(cB, cA)` and, if `x` is already determined, return the pinned
result wire `b`. Binds `x,b,m` from the single-term factors; checks the exact shape by list equality
(so a decode gives usable rewrite facts). `cB : (-1·x)(1·m) = (-1·ONE)+(1·b)`, `cA : (1·x)(1·b)=0`. -/
def izPin? (cB cA : Con F) (S : List ℕ) : Option ℕ :=
  match cA.L, cA.R, cB.R with
  | [(_, x)], [(_, b)], [(_, m)] =>
      if cA.L = [(1, x)] ∧ cA.R = [(1, b)] ∧ cA.O = [] ∧
         cB.L = [(-1, x)] ∧ cB.R = [(1, m)] ∧ cB.O = [(-1, 0), (1, b)] ∧ x ∈ S
      then some b else none
  | _, _, _ => none

/-- Decode a successful `izPin?`: it fixes the two constraints to the exact is-zero shape, with `x`
determined. -/
theorem izPin?_spec {cB cA : Con F} {S : List ℕ} {b : ℕ} (h : izPin? cB cA S = some b) :
    ∃ x m, cA.L = [(1, x)] ∧ cA.R = [(1, b)] ∧ cA.O = ([] : List (F × ℕ)) ∧
           cB.L = [((-1 : F), x)] ∧ cB.R = [(1, m)] ∧ cB.O = [((-1 : F), 0), (1, b)] ∧ x ∈ S := by
  unfold izPin? at h
  split at h
  next =>
    split at h
    next hcond =>
      obtain ⟨hAL, hAR, hAO, hBL, hBR, hBO, hxS⟩ := hcond
      cases Option.some.inj h
      exact ⟨_, _, hAL, hAR, hAO, hBL, hBR, hBO, hxS⟩
    next => simp at h
  next => simp at h

/-- One scan: consume the next constraint as a functional pin, or the next two as an is-zero pair. -/
def foldC : List (Con F) → List ℕ → List ℕ
  | [], S => S
  | [c], S => stepPin S c
  | cB :: cA :: rest, S =>
      match izPin? cB cA S with
      | some b => foldC rest (b :: S)
      | none   => foldC (cA :: rest) (stepPin S cB)

end Integrated

section IntegratedSound
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Integrated fold soundness.** With the ONE wire pinned (`a 0 = 1`), two satisfying assignments
agreeing on the inputs agree on every wire `foldC` determines — functional pins and is-zero results.
Needs the field (is-zero cancellation); for a concrete circuit, `ZMod p` with `[Fact (Nat.Prime p)]`. -/
theorem foldC_sound {a a' : ℕ → F} (h1 : a 0 = 1) (h1' : a' 0 = 1) :
    ∀ (cs : List (Con F)) (I : List ℕ),
      sat cs a → sat cs a' → agree I a a' → agree (foldC cs I) a a' := by
  intro cs I
  induction cs, I using foldC.induct with
  | case1 I => intro _ _ hI; simpa [foldC] using hI
  | case2 c I => intro ha ha' hI
                 have hc : holds c a := ha c (by simp)
                 have hc' : holds c a' := ha' c (by simp)
                 simpa [foldC] using stepPin_agree c I hc hc' hI
  | case3 cB cA rest I b hsome ih =>
      intro ha ha' hI
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hcA : holds cA a := ha cA (by simp)
      have hcA' : holds cA a' := ha' cA (by simp)
      have hsat : sat rest a := fun x hx => ha x (by simp [hx])
      have hsat' : sat rest a' := fun x hx => ha' x (by simp [hx])
      obtain ⟨x, m, hAL, hAR, hAO, hBL, hBR, hBO, hxI⟩ := izPin?_spec hsome
      have hx : a x = a' x := hI x hxI
      have h0 : a x * a b = 0 := by
        have := hcA; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have h0' : a' x * a' b = 0 := by
        have := hcA'; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have hh1 : a x * a m + a b = 1 := by
        have H := hcB; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1] at H
        linear_combination -H
      have hh1' : a' x * a' m + a' b = 1 := by
        have H := hcB'; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1'] at H
        linear_combination -H
      have hb : agree (b :: I) a a' := agree_cons (iszero_pin hx h0 hh1 h0' hh1') hI
      simpa [foldC, hsome] using ih hsat hsat' hb
  | case4 cB cA rest I hnone ih =>
      intro ha ha' hI
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hsat : sat (cA :: rest) a := fun x hx => ha x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hsat' : sat (cA :: rest) a' := fun x hx => ha' x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hstep : agree (stepPin I cB) a a' := stepPin_agree cB I hcB hcB' hI
      simpa [foldC, hnone] using ih hsat hsat' hstep

end IntegratedSound

/-!
## Guarded pins: the SAFE\* layer (determinacy modulo `divisor ≠ 0`)

gnark's quotient gadgets pin a wire `w` that sits ALONE (coeff 1) on one multiplicative side, with the
other side `D` (the divisor) and the output `O` already determined: `w · (D·a) = (O·a)`. Then `w` is
forced PROVIDED `D·a ≠ 0`. Unlike functional/is-zero, this carries a side-condition — so the fold
`foldG` returns not just the determined set but the LIST OF DIVISOR FORMS it leaned on. Those are the
`SAFE*` obligations, named precisely; `foldG_sound` gives determinacy **conditional** on every one being
nonzero (the hypothesis the inertness argument, `Inertness.lean`, discharges for the padding-zero cases).
-/
section GuardedDef
variable [DecidableEq F]

/-- Recognise a guarded pin: `w` alone with coeff 1 on `L`, divisor `R` and output `O` determined,
`w` new. Returns `(w, R)` — the pinned wire and the divisor form whose nonzero-ness is the obligation.
(L-side only: the dominant gnark shape; R-side quotients fail closed, leaving the wire undetermined.) -/
def gdPin? (c : R1CSChecker.Con F) (S : List ℕ) : Option (ℕ × List (F × ℕ)) :=
  match c.L with
  | [(cl, w)] =>
      if cl = 1 ∧ S.contains w = false ∧ wiresIn c.R S = true ∧ wiresIn c.O S = true
      then some (w, c.R) else none
  | _ => none

theorem gdPin?_spec {c : R1CSChecker.Con F} {S : List ℕ} {w : ℕ} {D : List (F × ℕ)}
    (h : gdPin? c S = some (w, D)) :
    c.L = [((1 : F), w)] ∧ D = c.R ∧ (∀ t ∈ c.R, t.2 ∈ S) ∧ (∀ t ∈ c.O, t.2 ∈ S) := by
  rw [gdPin?] at h
  rcases hL : c.L with _ | ⟨⟨cl, w2⟩, tl⟩
  · rw [hL] at h; exact absurd h (by simp)
  · rcases tl with _ | ⟨p2, tl2⟩
    · rw [hL] at h; simp only at h
      by_cases hcond : cl = 1 ∧ S.contains w2 = false ∧ wiresIn c.R S = true ∧ wiresIn c.O S = true
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hcl, _, hRb, hOb⟩ := hcond
        exact ⟨by rw [hcl], rfl, wiresIn_mem hRb, wiresIn_mem hOb⟩
      · rw [if_neg hcond] at h; exact absurd h (by simp)
    · rw [hL] at h; exact absurd h (by simp)

/-- One scan with guarded pins folded in: is-zero pair, else guarded pin (recording its divisor as an
obligation), else functional/no-op. Returns `(determined, obligations)`. -/
def foldG : List (R1CSChecker.Con F) → List ℕ → List (List (F × ℕ)) →
    List ℕ × List (List (F × ℕ))
  | [], S, ob => (S, ob)
  | [c], S, ob =>
      match gdPin? c S with
      | some (w, D) => (w :: S, D :: ob)
      | none => (stepPin S c, ob)
  | cB :: cA :: rest, S, ob =>
      match izPin? cB cA S with
      | some b => foldG rest (b :: S) ob
      | none =>
          match gdPin? cB S with
          | some (w, D) => foldG (cA :: rest) (w :: S) (D :: ob)
          | none => foldG (cA :: rest) (stepPin S cB) ob

/-- Obligations are only ACCUMULATED — every obligation present at a step survives to the end. So a
divisor recorded when a guarded pin fires is in the final obligation list (where `foldG_sound`'s
nonzero hypothesis ranges). -/
theorem foldG_obl_mono : ∀ (cs : List (R1CSChecker.Con F)) (S : List ℕ)
    (ob : List (List (F × ℕ))) (x : List (F × ℕ)), x ∈ ob → x ∈ (foldG cs S ob).2 := by
  intro cs S ob x
  induction cs, S, ob using foldG.induct with
  | case1 S ob => intro hx; exact hx
  | case2 c S ob w D hgd => intro hx; simp only [foldG, hgd]; exact List.mem_cons_of_mem _ hx
  | case3 c S ob hgd => intro hx; simp only [foldG, hgd]; exact hx
  | case4 cB cA rest S ob b hiz ih => intro hx; simp only [foldG, hiz]; exact ih hx
  | case5 cB cA rest S ob hiz w D hgd ih =>
      intro hx; simp only [foldG, hiz, hgd]; exact ih (List.mem_cons_of_mem _ hx)
  | case6 cB cA rest S ob hiz hgd ih => intro hx; simp only [foldG, hiz, hgd]; exact ih hx

end GuardedDef

section GuardedSound
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Per-step guarded soundness.** With the divisor value nonzero, a guarded pin determines `w`. -/
theorem gdPin_agree {c : R1CSChecker.Con F} {S : List ℕ} {w : ℕ} {D : List (F × ℕ)} {a a' : ℕ → F}
    (hc : holds c a) (hc' : holds c a') (hS : agree S a a')
    (hsome : gdPin? c S = some (w, D)) (hnz : dotp D a ≠ 0) : agree (w :: S) a a' := by
  obtain ⟨hL, hDR, hRw, hOw⟩ := gdPin?_spec hsome
  subst hDR
  have ha : a w * dotp c.R a = dotp c.O a := by
    have := hc; rw [holds, hL] at this; simpa [dotp] using this
  have ha' : a' w * dotp c.R a' = dotp c.O a' := by
    have := hc'; rw [holds, hL] at this; simpa [dotp] using this
  have hDeq : dotp c.R a = dotp c.R a' := dotp_agree hRw hS
  have hOeq : dotp c.O a = dotp c.O a' := dotp_agree hOw hS
  refine agree_cons ?_ hS
  have hcancel : a w * dotp c.R a = a' w * dotp c.R a := by rw [ha, hOeq, ← ha', hDeq]
  exact mul_right_cancel₀ hnz hcancel

/-- **Guarded fold soundness (the SAFE\* form).** With the ONE wire pinned and EVERY recorded divisor
nonzero on `a`, two satisfying assignments agreeing on the inputs agree on every wire `foldG`
determines — functional, is-zero, AND guarded pins. The nonzero hypotheses are the named `SAFE*`
residual (discharged by `Inertness.lean`). -/
theorem foldG_sound {a a' : ℕ → F} (h1 : a 0 = 1) (h1' : a' 0 = 1) :
    ∀ (cs : List (R1CSChecker.Con F)) (S : List ℕ) (ob : List (List (F × ℕ))),
      sat cs a → sat cs a' → agree S a a' →
      (∀ D ∈ (foldG cs S ob).2, dotp D a ≠ 0) →
      agree (foldG cs S ob).1 a a' := by
  intro cs S ob
  induction cs, S, ob using foldG.induct with
  | case1 S ob => intro _ _ hS _; exact hS
  | case2 c S ob w D hgd =>
      intro ha ha' hS hnz
      have hc : holds c a := ha c (by simp)
      have hc' : holds c a' := ha' c (by simp)
      simp only [foldG, hgd] at hnz ⊢
      have hD : dotp D a ≠ 0 := hnz D (by simp)
      exact gdPin_agree hc hc' hS hgd hD
  | case3 c S ob hgd =>
      intro ha ha' hS _
      have hc : holds c a := ha c (by simp)
      have hc' : holds c a' := ha' c (by simp)
      simp only [foldG, hgd]
      exact stepPin_agree c S hc hc' hS
  | case4 cB cA rest S ob b hiz ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hcA : holds cA a := ha cA (by simp)
      have hcA' : holds cA a' := ha' cA (by simp)
      have hsat : sat rest a := fun x hx => ha x (by simp [hx])
      have hsat' : sat rest a' := fun x hx => ha' x (by simp [hx])
      obtain ⟨x, m, hAL, hAR, hAO, hBL, hBR, hBO, hxI⟩ := izPin?_spec hiz
      have hx : a x = a' x := hS x hxI
      have h0 : a x * a b = 0 := by
        have := hcA; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have h0' : a' x * a' b = 0 := by
        have := hcA'; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have hh1 : a x * a m + a b = 1 := by
        have H := hcB; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1] at H
        linear_combination -H
      have hh1' : a' x * a' m + a' b = 1 := by
        have H := hcB'; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1'] at H
        linear_combination -H
      have hb : agree (b :: S) a a' := agree_cons (iszero_pin hx h0 hh1 h0' hh1') hS
      simp only [foldG, hiz] at hnz ⊢
      exact ih hsat hsat' hb hnz
  | case5 cB cA rest S ob hiz w D hgd ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hsat : sat (cA :: rest) a := fun x hx => ha x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hsat' : sat (cA :: rest) a' := fun x hx => ha' x (by simp [List.mem_cons] at hx ⊢; tauto)
      simp only [foldG, hiz, hgd] at hnz ⊢
      have hD : dotp D a ≠ 0 := hnz D (foldG_obl_mono _ _ _ D (by simp))
      have hw : agree (w :: S) a a' := gdPin_agree hcB hcB' hS hgd hD
      exact ih hsat hsat' hw hnz
  | case6 cB cA rest S ob hiz hgd ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hsat : sat (cA :: rest) a := fun x hx => ha x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hsat' : sat (cA :: rest) a' := fun x hx => ha' x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hstep : agree (stepPin S cB) a a' := stepPin_agree cB S hcB hcB' hS
      simp only [foldG, hiz, hgd] at hnz ⊢
      exact ih hsat hsat' hstep hnz

end GuardedSound

/-!
## Bit-decomposition determinacy (the canonicity core)

The range-check / comparator gadgets pin a group of BIT wires `b₀…b_{n-1}` by two facts: each is
BOOLEAN (`bᵢ·(bᵢ−1) = 0`) and they RECOMPOSE a determined value (`Σ 2ⁱ·bᵢ = value`). Unlike the
functional/is-zero/guarded leaves this is not a local 1–2 constraint pattern but a scattered GROUP,
and its determinacy is the CANONICITY theorem: a value has a unique binary expansion **only** when
there is no wraparound (`2ⁿ ≤ p`). `bits_agree` is that determinacy, kernel-checked in the list model:
parity forces the least bit, halve and recurse (`natVal_inj`), lifted from ℕ to `ZMod p` through the
no-wraparound bound. It is the reusable determinacy fact a certificate composes per bit-group (the
fold's linear scan cannot see a scattered group, so bit-decomposition is discharged at composition
time, not as a `foldG` step).
-/
namespace BitDec

/-- Value of a bit list, LSB first: `Σ 2ⁱ·bits[i]` over ℕ. -/
def natVal : List ℕ → ℕ
  | [] => 0
  | b :: bs => b + 2 * natVal bs

/-- Binary uniqueness over ℕ: equal-length {0,1}-lists with equal value are equal. -/
theorem natVal_inj : ∀ {u v : List ℕ}, u.length = v.length →
    (∀ b ∈ u, b = 0 ∨ b = 1) → (∀ b ∈ v, b = 0 ∨ b = 1) → natVal u = natVal v → u = v := by
  intro u
  induction u with
  | nil => intro v hlen _ _ _; cases v with | nil => rfl | cons => simp at hlen
  | cons b bs ih =>
      intro v hlen hu hv hval
      cases v with
      | nil => simp at hlen
      | cons c cs =>
        simp only [natVal] at hval
        have hb := hu b (by simp); have hc := hv c (by simp)
        have hbc : b = c := by rcases hb with h|h <;> rcases hc with h'|h' <;> omega
        subst hbc
        have hrec : natVal bs = natVal cs := by omega
        rw [ih (by simpa using hlen) (fun x hx => hu x (by simp [hx]))
              (fun x hx => hv x (by simp [hx])) hrec]

theorem natVal_lt : ∀ (u : List ℕ), (∀ b ∈ u, b = 0 ∨ b = 1) → natVal u < 2 ^ u.length := by
  intro u; induction u with
  | nil => intro _; simp [natVal]
  | cons b bs ih =>
      intro hu
      have hb := hu b (by simp)
      have := ih (fun x hx => hu x (by simp [hx]))
      simp only [natVal, List.length_cons, pow_succ]
      rcases hb with h|h <;> subst h <;> omega

variable {p : ℕ}

/-- `ZMod p` recomposition value `Σ 2ⁱ·a(bits[i])` (LSB first) — the value the recomposition
constraint `(ONE)·(Σ 2ⁱ·bᵢ) = value` equates to `value`. -/
def zVal (bits : List ℕ) (a : ℕ → ZMod p) : ZMod p :=
  match bits with
  | [] => 0
  | b :: bs => a b + 2 * zVal bs a

/-- The ℕ bit of a boolean `ZMod p` value. -/
noncomputable def nb (a : ℕ → ZMod p) (b : ℕ) : ℕ := if a b = 1 then 1 else 0

theorem zVal_cast [Fact (Nat.Prime p)] {bits : List ℕ} {a : ℕ → ZMod p}
    (hbool : ∀ b ∈ bits, a b = 0 ∨ a b = 1) :
    zVal bits a = ((natVal (bits.map (nb a)) : ℕ) : ZMod p) := by
  induction bits with
  | nil => simp [zVal, natVal]
  | cons b bs ih =>
      simp only [zVal, List.map_cons, natVal, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      rw [ih (fun x hx => hbool x (by simp [hx]))]
      rcases hbool b (by simp) with h | h <;> simp [nb, h]

/-- Booleanity bridge: the raw gnark constraint `b·(1−b) = 0` gives `a b ∈ {0,1}`. -/
theorem bool_of_bc [Fact (Nat.Prime p)] {b : ℕ} {a : ℕ → ZMod p} (h : a b * (1 - a b) = 0) : a b = 0 ∨ a b = 1 := by
  rcases mul_eq_zero.1 h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.1 h1).symm

/-- **Bit-decomposition determinacy.** Booleanity on both runs, a shared recomposition value, and
no wraparound (`2ⁿ ≤ p`) force every bit to agree — the canonicity theorem in the list model. -/
theorem bits_agree [Fact (Nat.Prime p)] {bits : List ℕ} {a a' : ℕ → ZMod p}
    (hbool : ∀ b ∈ bits, a b = 0 ∨ a b = 1) (hbool' : ∀ b ∈ bits, a' b = 0 ∨ a' b = 1)
    (hval : zVal bits a = zVal bits a') (hcanon : 2 ^ bits.length ≤ p) :
    ∀ b ∈ bits, a b = a' b := by
  have hbu : ∀ x ∈ bits.map (nb a), x = 0 ∨ x = 1 := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; unfold nb; split <;> simp
  have hbu' : ∀ x ∈ bits.map (nb a'), x = 0 ∨ x = 1 := by
    intro x hx; simp only [List.mem_map] at hx; obtain ⟨b, _, rfl⟩ := hx; unfold nb; split <;> simp
  have hcast : ((natVal (bits.map (nb a)) : ℕ) : ZMod p)
      = ((natVal (bits.map (nb a')) : ℕ) : ZMod p) := by
    rw [← zVal_cast hbool, ← zVal_cast hbool', hval]
  have hlt : natVal (bits.map (nb a)) < p :=
    lt_of_lt_of_le (by simpa using natVal_lt _ hbu) (by simpa using hcanon)
  have hlt' : natVal (bits.map (nb a')) < p :=
    lt_of_lt_of_le (by simpa using natVal_lt _ hbu') (by simpa using hcanon)
  have hnateq : natVal (bits.map (nb a)) = natVal (bits.map (nb a')) := by
    have := congrArg (ZMod.val) hcast
    rwa [ZMod.val_natCast_of_lt hlt, ZMod.val_natCast_of_lt hlt'] at this
  have hmaps : bits.map (nb a) = bits.map (nb a') :=
    natVal_inj (by simp) hbu hbu' hnateq
  intro b hb
  have hnbeq : nb a b = nb a' b := List.map_eq_map_iff.1 hmaps b hb
  unfold nb at hnbeq
  rcases hbool b hb with h | h <;> rcases hbool' b hb with h' | h' <;> simp [h, h'] at hnbeq ⊢

end BitDec

/-!
## The scalable fold: an `Array Bool` determined set (linear, `native_decide`-friendly)

`foldC`/`foldG` carry the determined set as a `List ℕ`, so `wiresIn` does an O(|S|) `List.contains` per
term and the whole scan is O(n²) — `native_decide` stalls past a few hundred constraints. `foldB` is the
same scan with the determined set as an **`Array Bool`** indexed by wire id: membership and marking are
O(1), so the scan is linear and `native_decide` computes the determined set of a 6k-constraint circuit in
well under a second. The soundness is identical in shape to `foldG_sound` — the field cores `iszero_pin`
and `guarded_pin` are reused verbatim (they speak of `a x`, not of the set representation); only the
membership abstraction changes (`agreeA` over `Array.getD`, closed under `agreeA_set`).
-/
section FastDef
variable [DecidableEq F]

/-- Membership in the `Array Bool` determined set. -/
def memB (S : Array Bool) (v : ℕ) : Prop := S.getD v false = true

/-- The two runs agree on every wire the `Array Bool` set marks determined. -/
def agreeA (S : Array Bool) (a a' : ℕ → F) : Prop := ∀ v, memB S v → a v = a' v

/-- All wires of a linear form are marked determined. Decidable, O(|l|). -/
def winB (l : List (F × ℕ)) (S : Array Bool) : Bool := l.all (fun t => S.getD t.2 false)

theorem winB_mem {l : List (F × ℕ)} {S : Array Bool} (h : winB l S = true) :
    ∀ t ∈ l, memB S t.2 := fun t ht => (List.all_eq_true.1 h) t ht

theorem dotp_agreeA {l : List (F × ℕ)} {S : Array Bool} {a a' : ℕ → F}
    (hl : winB l S = true) (h : agreeA S a a') : dotp l a = dotp l a' := by
  induction l with
  | nil => rfl
  | cons t ts ih =>
    have hts : winB ts S = true := by
      simp only [winB, List.all_cons, Bool.and_eq_true] at hl; exact hl.2
    rw [dotp_cons, dotp_cons, ih hts, h t.2 (winB_mem hl t (by simp))]

theorem getD_setIfInBounds_ne (S : Array Bool) {w v : ℕ} (hvw : v ≠ w) :
    (S.setIfInBounds w true).getD v false = S.getD v false := by
  rw [Array.getD_eq_get?, Array.getD_eq_get?, Array.setIfInBounds]
  split
  · rw [Array.getElem?_set_ne]; omega
  · rfl

theorem agreeA_set {S : Array Bool} {w : ℕ} {a a' : ℕ → F}
    (hw : a w = a' w) (hS : agreeA S a a') : agreeA (S.setIfInBounds w true) a a' := by
  intro v hv
  by_cases hvw : v = w
  · subst hvw; exact hw
  · exact hS v (by unfold memB at hv ⊢; rwa [getD_setIfInBounds_ne S hvw] at hv)

/-- Functional pin over the `Array Bool` set — the pinned wire is the coeff-1 head of `O`, everything
else marked determined, the wire new. -/
def funPinB? (c : R1CSChecker.Con F) (S : Array Bool) : Option ℕ :=
  match c.O with
  | (t :: Orest) =>
      if t.1 = 1 ∧ S.getD t.2 false = false ∧ winB c.L S ∧ winB c.R S ∧ winB Orest S
      then some t.2 else none
  | [] => none

/-- One functional-or-noop step. -/
def stepB (S : Array Bool) (c : R1CSChecker.Con F) : Array Bool :=
  match funPinB? c S with
  | some w => S.setIfInBounds w true
  | none => S

/-- is-zero recogniser over the `Array Bool` set (same shape as `izPin?`, Array membership for `x`). -/
def izPinB? (cB cA : R1CSChecker.Con F) (S : Array Bool) : Option ℕ :=
  match cA.L, cA.R, cB.R with
  | [(_, x)], [(_, b)], [(_, m)] =>
      if cA.L = [(1, x)] ∧ cA.R = [(1, b)] ∧ cA.O = [] ∧
         cB.L = [(-1, x)] ∧ cB.R = [(1, m)] ∧ cB.O = [(-1, 0), (1, b)] ∧ S.getD x false = true
      then some b else none
  | _, _, _ => none

theorem izPinB?_spec {cB cA : R1CSChecker.Con F} {S : Array Bool} {b : ℕ} (h : izPinB? cB cA S = some b) :
    ∃ x m, cA.L = [(1, x)] ∧ cA.R = [(1, b)] ∧ cA.O = ([] : List (F × ℕ)) ∧
           cB.L = [((-1 : F), x)] ∧ cB.R = [(1, m)] ∧ cB.O = [((-1 : F), 0), (1, b)] ∧ memB S x := by
  unfold izPinB? at h
  split at h
  next =>
    split at h
    next hcond =>
      obtain ⟨hAL, hAR, hAO, hBL, hBR, hBO, hxS⟩ := hcond
      cases Option.some.inj h
      exact ⟨_, _, hAL, hAR, hAO, hBL, hBR, hBO, hxS⟩
    next => simp at h
  next => simp at h

/-- guarded recogniser over the `Array Bool` set (same shape as `gdPin?`, Array membership). -/
def gdPinB? (c : R1CSChecker.Con F) (S : Array Bool) : Option (ℕ × List (F × ℕ)) :=
  match c.L with
  | [(cl, w)] =>
      if cl = 1 ∧ S.getD w false = false ∧ winB c.R S = true ∧ winB c.O S = true
      then some (w, c.R) else none
  | _ => none

theorem gdPinB?_spec {c : R1CSChecker.Con F} {S : Array Bool} {w : ℕ} {D : List (F × ℕ)}
    (h : gdPinB? c S = some (w, D)) :
    c.L = [((1 : F), w)] ∧ D = c.R ∧ winB c.R S = true ∧ winB c.O S = true := by
  rw [gdPinB?] at h
  rcases hL : c.L with _ | ⟨⟨cl, w2⟩, tl⟩
  · rw [hL] at h; exact absurd h (by simp)
  · rcases tl with _ | ⟨p2, tl2⟩
    · rw [hL] at h; simp only at h
      by_cases hcond : cl = 1 ∧ S.getD w2 false = false ∧ winB c.R S = true ∧ winB c.O S = true
      · rw [if_pos hcond] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hcl, _, hRb, hOb⟩ := hcond
        exact ⟨by rw [hcl], rfl, hRb, hOb⟩
      · rw [if_neg hcond] at h; exact absurd h (by simp)
    · rw [hL] at h; exact absurd h (by simp)

/-- The scalable scan: is-zero pair, else guarded pin (recording its divisor), else functional/no-op —
determined set as an `Array Bool`. Returns `(marks, obligations)`. -/
def foldB : List (R1CSChecker.Con F) → Array Bool → List (List (F × ℕ)) →
    Array Bool × List (List (F × ℕ))
  | [], S, ob => (S, ob)
  | [c], S, ob =>
      match gdPinB? c S with
      | some (w, D) => (S.setIfInBounds w true, D :: ob)
      | none => (stepB S c, ob)
  | cB :: cA :: rest, S, ob =>
      match izPinB? cB cA S with
      | some b => foldB rest (S.setIfInBounds b true) ob
      | none =>
          match gdPinB? cB S with
          | some (w, D) => foldB (cA :: rest) (S.setIfInBounds w true) (D :: ob)
          | none => foldB (cA :: rest) (stepB S cB) ob

theorem foldB_obl_mono : ∀ (cs : List (R1CSChecker.Con F)) (S : Array Bool)
    (ob : List (List (F × ℕ))) (x : List (F × ℕ)), x ∈ ob → x ∈ (foldB cs S ob).2 := by
  intro cs S ob x
  induction cs, S, ob using foldB.induct with
  | case1 S ob => intro hx; exact hx
  | case2 c S ob w D hgd => intro hx; simp only [foldB, hgd]; exact List.mem_cons_of_mem _ hx
  | case3 c S ob hgd => intro hx; simp only [foldB, hgd]; exact hx
  | case4 cB cA rest S ob b hiz ih => intro hx; simp only [foldB, hiz]; exact ih hx
  | case5 cB cA rest S ob hiz w D hgd ih =>
      intro hx; simp only [foldB, hiz, hgd]; exact ih (List.mem_cons_of_mem _ hx)
  | case6 cB cA rest S ob hiz hgd ih => intro hx; simp only [foldB, hiz, hgd]; exact ih hx

end FastDef

section FastSound
variable {F : Type*} [Field F] [DecidableEq F]

theorem funPinB?_agree {c : R1CSChecker.Con F} {S : Array Bool} {w : ℕ} {a a' : ℕ → F}
    (hc : holds c a) (hc' : holds c a') (hS : agreeA S a a') (h : funPinB? c S = some w) :
    a w = a' w := by
  unfold funPinB? at h
  rcases hO : c.O with _ | ⟨t, Orest⟩
  · rw [hO] at h; simp at h
  · rw [hO] at h; simp only at h
    by_cases hcond : t.1 = 1 ∧ S.getD t.2 false = false ∧ winB c.L S ∧ winB c.R S ∧ winB Orest S
    · rw [if_pos hcond] at h; obtain ⟨h1, _, hLb, hRb, hOb⟩ := hcond
      cases h
      have pin : ∀ b : ℕ → F, holds c b → dotp c.L b * dotp c.R b = b t.2 + dotp Orest b := by
        intro b hb; simp only [holds, hO, dotp_cons, h1, one_mul] at hb; exact hb
      have e1 := pin a hc; have e2 := pin a' hc'
      rw [dotp_agreeA hLb hS, dotp_agreeA hRb hS, dotp_agreeA hOb hS] at e1
      exact add_right_cancel (e1.symm.trans e2)
    · rw [if_neg hcond] at h; simp at h

theorem stepB_agree (c : R1CSChecker.Con F) (S : Array Bool) {a a' : ℕ → F}
    (hc : holds c a) (hc' : holds c a') (hS : agreeA S a a') : agreeA (stepB S c) a a' := by
  unfold stepB
  cases h : funPinB? c S with
  | some w => exact agreeA_set (funPinB?_agree hc hc' hS h) hS
  | none => exact hS

theorem gdPinB_agree {c : R1CSChecker.Con F} {S : Array Bool} {w : ℕ} {D : List (F × ℕ)} {a a' : ℕ → F}
    (hc : holds c a) (hc' : holds c a') (hS : agreeA S a a')
    (hsome : gdPinB? c S = some (w, D)) (hnz : dotp D a ≠ 0) : agreeA (S.setIfInBounds w true) a a' := by
  obtain ⟨hL, hDR, hRw, hOw⟩ := gdPinB?_spec hsome
  subst hDR
  have ha : a w * dotp c.R a = dotp c.O a := by
    have := hc; rw [holds, hL] at this; simpa [dotp] using this
  have ha' : a' w * dotp c.R a' = dotp c.O a' := by
    have := hc'; rw [holds, hL] at this; simpa [dotp] using this
  have hDeq : dotp c.R a = dotp c.R a' := dotp_agreeA hRw hS
  have hOeq : dotp c.O a = dotp c.O a' := dotp_agreeA hOw hS
  refine agreeA_set ?_ hS
  exact mul_right_cancel₀ hnz (by rw [ha, hOeq, ← ha', hDeq])

/-- **Scalable fold soundness.** Identical guarantee to `foldG_sound` — with the ONE wire pinned and
every recorded divisor nonzero, two satisfying assignments agreeing on the inputs agree on every wire
`foldB` marks (functional, is-zero, guarded) — but over the O(1)-membership `Array Bool` set, so
`native_decide` scales to real circuits. -/
theorem foldB_sound {a a' : ℕ → F} (h1 : a 0 = 1) (h1' : a' 0 = 1) :
    ∀ (cs : List (R1CSChecker.Con F)) (S : Array Bool) (ob : List (List (F × ℕ))),
      sat cs a → sat cs a' → agreeA S a a' →
      (∀ D ∈ (foldB cs S ob).2, dotp D a ≠ 0) →
      agreeA (foldB cs S ob).1 a a' := by
  intro cs S ob
  induction cs, S, ob using foldB.induct with
  | case1 S ob => intro _ _ hS _; exact hS
  | case2 c S ob w D hgd =>
      intro ha ha' hS hnz
      have hc : holds c a := ha c (by simp)
      have hc' : holds c a' := ha' c (by simp)
      simp only [foldB, hgd] at hnz ⊢
      exact gdPinB_agree hc hc' hS hgd (hnz D (by simp))
  | case3 c S ob hgd =>
      intro ha ha' hS _
      have hc : holds c a := ha c (by simp)
      have hc' : holds c a' := ha' c (by simp)
      simp only [foldB, hgd]
      exact stepB_agree c S hc hc' hS
  | case4 cB cA rest S ob b hiz ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hcA : holds cA a := ha cA (by simp)
      have hcA' : holds cA a' := ha' cA (by simp)
      have hsat : sat rest a := fun x hx => ha x (by simp [hx])
      have hsat' : sat rest a' := fun x hx => ha' x (by simp [hx])
      obtain ⟨x, m, hAL, hAR, hAO, hBL, hBR, hBO, hxI⟩ := izPinB?_spec hiz
      have hx : a x = a' x := hS x hxI
      have h0 : a x * a b = 0 := by
        have := hcA; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have h0' : a' x * a' b = 0 := by
        have := hcA'; rw [holds, hAL, hAR, hAO] at this; simpa [dotp] using this
      have hh1 : a x * a m + a b = 1 := by
        have H := hcB; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1] at H
        linear_combination -H
      have hh1' : a' x * a' m + a' b = 1 := by
        have H := hcB'; rw [holds, hBL, hBR, hBO] at H
        simp only [dotp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1'] at H
        linear_combination -H
      have hb : agreeA (S.setIfInBounds b true) a a' :=
        agreeA_set (iszero_pin hx h0 hh1 h0' hh1') hS
      simp only [foldB, hiz] at hnz ⊢
      exact ih hsat hsat' hb hnz
  | case5 cB cA rest S ob hiz w D hgd ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hsat : sat (cA :: rest) a := fun x hx => ha x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hsat' : sat (cA :: rest) a' := fun x hx => ha' x (by simp [List.mem_cons] at hx ⊢; tauto)
      simp only [foldB, hiz, hgd] at hnz ⊢
      have hD : dotp D a ≠ 0 := hnz D (foldB_obl_mono _ _ _ D (by simp))
      exact ih hsat hsat' (gdPinB_agree hcB hcB' hS hgd hD) hnz
  | case6 cB cA rest S ob hiz hgd ih =>
      intro ha ha' hS hnz
      have hcB : holds cB a := ha cB (by simp)
      have hcB' : holds cB a' := ha' cB (by simp)
      have hsat : sat (cA :: rest) a := fun x hx => ha x (by simp [List.mem_cons] at hx ⊢; tauto)
      have hsat' : sat (cA :: rest) a' := fun x hx => ha' x (by simp [List.mem_cons] at hx ⊢; tauto)
      simp only [foldB, hiz, hgd] at hnz ⊢
      exact ih hsat hsat' (stepB_agree cB S hcB hcB' hS) hnz

end FastSound

/-!
## Bit-decomposition over the constraint form (composed into the fold's determined set)

`BitDec.bits_agree` is the canonicity core over the abstract recomposition value `zVal`. To USE it on a
real circuit — whose recomposition constraint is `(ONE)·(Σ 2ⁱ·bᵢ) = val` — we bridge `zVal` to the
`dotp` of the power-of-two coefficient list (`dotp_powList`), then `bitLeaf_agree` discharges a bit group
from: booleanity on both runs, the recomposition equation, and `val` marked determined in the `Array Bool`
set. This is the leaf the fixpoint marker applies per group (bit decomposition is a scattered group, so it
is composed after the scan rather than inside it).
-/
namespace BitDec
variable {p : ℕ}

/-- The power-of-two coefficient list for a bit list (LSB first): `[(1,b₀),(2,b₁),(4,b₂),…]`. -/
def powList : List ℕ → List (ZMod p × ℕ)
  | [] => []
  | b :: bs => (1, b) :: (powList bs).map (fun t => (2 * t.1, t.2))

theorem dotp_map_double (l : List (ZMod p × ℕ)) (a : ℕ → ZMod p) :
    R1CSChecker.dotp (l.map (fun t => (2 * t.1, t.2))) a = 2 * R1CSChecker.dotp l a := by
  induction l with
  | nil => simp [R1CSChecker.dotp]
  | cons t ts ih => simp only [List.map_cons, R1CSChecker.dotp_cons, ih]; ring

theorem dotp_powList (bits : List ℕ) (a : ℕ → ZMod p) :
    R1CSChecker.dotp (powList bits) a = zVal bits a := by
  induction bits with
  | nil => simp [powList, R1CSChecker.dotp, zVal]
  | cons b bs ih => simp only [powList, R1CSChecker.dotp_cons, dotp_map_double, ih, zVal, one_mul]

/-- **Bit-leaf determinacy, constraint form.** Booleanity on both runs, the recomposition equation
`(powList bits)·a = val·a`, and `val` marked determined ⇒ the bits agree. Reuses `bits_agree`. -/
theorem bitLeaf_agree [Fact (Nat.Prime p)] {bits : List ℕ} {val : List (ZMod p × ℕ)} {S : Array Bool} {a a' : ℕ → ZMod p}
    (hbool : ∀ b ∈ bits, a b * (1 - a b) = 0) (hbool' : ∀ b ∈ bits, a' b * (1 - a' b) = 0)
    (hrec : R1CSChecker.dotp (powList bits) a = R1CSChecker.dotp val a)
    (hrec' : R1CSChecker.dotp (powList bits) a' = R1CSChecker.dotp val a')
    (hval : R1CSChecker.winB val S = true) (hS : R1CSChecker.agreeA S a a')
    (hcanon : 2 ^ bits.length ≤ p) : ∀ b ∈ bits, a b = a' b := by
  refine bits_agree (fun b hb => bool_of_bc (hbool b hb)) (fun b hb => bool_of_bc (hbool' b hb)) ?_ hcanon
  rw [← dotp_powList, ← dotp_powList, hrec, hrec', R1CSChecker.dotp_agreeA hval hS]

end BitDec

/-!
## The full determined set: scan + bit-decomposition to a fixpoint

Bit decomposition and functional/guarded pins are mutually recursive — a pinned value unlocks its bits
(`bitLeaf_agree`), and pinned bits unlock downstream functional pins (`foldB`). `fullFold` iterates the two
to a fixpoint (`fuel` rounds), and `fullFold_sound` composes `foldB_sound` with the bit-group marker
`bitMark_agree`. The per-group facts `grpOk` (booleanity + recomposition + no wraparound) are exactly what
a circuit's booleanity and recomposition constraints supply via `sat`, discharged by the codegen.
-/
section BitMark
variable {p : ℕ}

/-- Mark every wire of `bits` determined in the `Array Bool` set. -/
def markBits (bits : List ℕ) (S : Array Bool) : Array Bool :=
  bits.foldl (fun S b => S.setIfInBounds b true) S

theorem markBits_agree [Fact (Nat.Prime p)] {bits : List ℕ} {S : Array Bool} {a a' : ℕ → ZMod p}
    (hbits : ∀ b ∈ bits, a b = a' b) (hS : agreeA S a a') : agreeA (markBits bits S) a a' := by
  unfold markBits
  induction bits generalizing S with
  | nil => simpa using hS
  | cons b bs ih =>
      simp only [List.foldl_cons]
      exact ih (fun x hx => hbits x (by simp [hx])) (agreeA_set (hbits b (by simp)) hS)

/-- A bit group: its bit wires (LSB first) and the recomposition value form. -/
abbrev BitGrp (p : ℕ) := List ℕ × List (ZMod p × ℕ)

/-- The per-group facts a bit group needs — booleanity on both runs, the recomposition equation on
both, and no wraparound. Supplied from `sat cs` + `a 0 = 1` by the codegen. -/
def grpOk (g : BitGrp p) (a a' : ℕ → ZMod p) : Prop :=
  (∀ b ∈ g.1, a b * (1 - a b) = 0) ∧ (∀ b ∈ g.1, a' b * (1 - a' b) = 0) ∧
  R1CSChecker.dotp (BitDec.powList g.1) a = R1CSChecker.dotp g.2 a ∧
  R1CSChecker.dotp (BitDec.powList g.1) a' = R1CSChecker.dotp g.2 a' ∧ 2 ^ g.1.length ≤ p

/-- Mark the bits of every group whose value form is already determined. -/
def bitMark (groups : List (BitGrp p)) (S : Array Bool) : Array Bool :=
  groups.foldl (fun S g => if winB g.2 S then markBits g.1 S else S) S

theorem bitMark_agree [Fact (Nat.Prime p)] {groups : List (BitGrp p)} {S : Array Bool} {a a' : ℕ → ZMod p}
    (hg : ∀ g ∈ groups, grpOk g a a') (hS : agreeA S a a') : agreeA (bitMark groups S) a a' := by
  unfold bitMark
  induction groups generalizing S with
  | nil => simpa using hS
  | cons g gs ih =>
      simp only [List.foldl_cons]
      apply ih (fun x hx => hg x (by simp [hx]))
      by_cases hv : winB g.2 S
      · rw [if_pos hv]; obtain ⟨hb, hb', hr, hr', hc⟩ := hg g (by simp)
        exact markBits_agree (BitDec.bitLeaf_agree hb hb' hr hr' hv hS hc) hS
      · rw [if_neg hv]; exact hS

/-- **Fixpoint fold**: alternate the scan `foldB` and the bit-group marker `bitMark` for `fuel` rounds. -/
def fullFold (cs : List (R1CSChecker.Con (ZMod p))) (groups : List (BitGrp p)) :
    ℕ → Array Bool → List (List (ZMod p × ℕ)) → Array Bool × List (List (ZMod p × ℕ))
  | 0, S, ob => (S, ob)
  | k+1, S, ob => let r := foldB cs S ob; fullFold cs groups k (bitMark groups r.1) r.2

theorem fullFold_obl_mono (cs) (groups : List (BitGrp p)) :
    ∀ (fuel) (S) (ob) (x), x ∈ ob → x ∈ (fullFold cs groups fuel S ob).2 := by
  intro fuel
  induction fuel with
  | zero => intro S ob x hx; exact hx
  | succ k ih => intro S ob x hx; simp only [fullFold]; exact ih _ _ x (foldB_obl_mono cs S ob x hx)

/-- **Full determinacy.** With the ONE wire pinned, every recorded divisor nonzero, and every bit group
valid, two satisfying assignments agreeing on the inputs agree on the entire fixpoint determined set —
functional, is-zero, guarded, AND bit decomposition. -/
theorem fullFold_sound [Fact (Nat.Prime p)] {a a' : ℕ → ZMod p} (h1 : a 0 = 1) (h1' : a' 0 = 1)
    (cs : List (R1CSChecker.Con (ZMod p))) (groups : List (BitGrp p))
    (ha : sat cs a) (ha' : sat cs a') (hg : ∀ g ∈ groups, grpOk g a a') :
    ∀ (fuel) (S) (ob), agreeA S a a' →
      (∀ D ∈ (fullFold cs groups fuel S ob).2, R1CSChecker.dotp D a ≠ 0) →
      agreeA (fullFold cs groups fuel S ob).1 a a' := by
  intro fuel
  induction fuel with
  | zero => intro S ob hS _; simpa [fullFold] using hS
  | succ k ih =>
      intro S ob hS hnz
      simp only [fullFold] at hnz ⊢
      have hnz_r : ∀ D ∈ (foldB cs S ob).2, R1CSChecker.dotp D a ≠ 0 :=
        fun D hD => hnz D (fullFold_obl_mono cs groups k _ _ D hD)
      exact ih _ _ (bitMark_agree hg (foldB_sound h1 h1' cs S ob ha ha' hS hnz_r)) hnz

/-- The canonical booleanity constraint for a bit wire: `b·(1−b) = 0`. -/
def boolCon (b : ℕ) : R1CSChecker.Con (ZMod p) := ⟨[(1, b)], [(1, 0), (-1, b)], []⟩

/-- The canonical recomposition constraint for a group: `(ONE)·(Σ 2ⁱ·bᵢ) = val`. -/
def recompCon (g : BitGrp p) : R1CSChecker.Con (ZMod p) := ⟨[(1, 0)], BitDec.powList g.1, g.2⟩

/-- Decidable well-formedness: a group's booleanity constraints and recomposition constraint are all
members of `cs`, and there is no wraparound. When true, `sat cs` supplies `grpOk` (`grpOk_of_sat`). -/
def grpWF (g : BitGrp p) (cs : List (R1CSChecker.Con (ZMod p))) : Bool :=
  g.1.all (fun b => decide (boolCon b ∈ cs)) && decide (recompCon g ∈ cs) &&
  decide (2 ^ g.1.length ≤ p)

/-- **The bit-group discharge.** A well-formed group's facts (`grpOk`) follow from `sat cs` and
`a 0 = 1` — its booleanity and recomposition constraints hold because they are in `cs`. So the codegen
proves `grpWF` by `native_decide` (structural) and gets `grpOk` for free. -/
theorem grpOk_of_sat [Fact (Nat.Prime p)] {a a' : ℕ → ZMod p} (h1 : a 0 = 1) (h1' : a' 0 = 1)
    {cs : List (R1CSChecker.Con (ZMod p))} (ha : sat cs a) (ha' : sat cs a')
    {g : BitGrp p} (hwf : grpWF g cs = true) : grpOk g a a' := by
  unfold grpWF at hwf
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hwf
  obtain ⟨⟨hbmem, hrmem⟩, hcanon⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_, hcanon⟩
  · intro b hb
    have H := ha _ (hbmem b hb)
    simp only [holds, boolCon, dotp_cons, dotp_nil, h1] at H; linear_combination H
  · intro b hb
    have H := ha' _ (hbmem b hb)
    simp only [holds, boolCon, dotp_cons, dotp_nil, h1'] at H; linear_combination H
  · have H := ha _ hrmem
    simp only [holds, recompCon, dotp_cons, dotp_nil, h1] at H; linear_combination H
  · have H := ha' _ hrmem
    simp only [holds, recompCon, dotp_cons, dotp_nil, h1'] at H; linear_combination H

end BitMark

/-!
## Parsing large circuits from a `String` (the frontend that actually scales)

Embedding a real circuit as a `List (Con (ZMod p))` LITERAL does not scale — Lean elaborates a
multi-thousand-element list literal superlinearly (and `ZMod p` numerals force per-element `whnf`),
timing out well before 6k constraints. A `String` literal, by contrast, is a primitive elaborated in
O(n). So the codegen emits the circuit as a flat integer string and `parseCons` decodes it into `cs`
at compute time; `native_decide` compiles the parse + `foldB` and runs both in seconds. `parseCons` is
total (structural on the constraint-count fuel); the determinacy theorem is about whatever `cs` it
produces, so parser faithfulness sits on the same trust line as literal emission.
-/
section Parse
variable [CommRing F]

/-- Read `n` `(coeff, wire)` pairs off the token stream (coeffs cast `Int → F`). -/
def takePairs : ℕ → List Int → List (F × ℕ) × List Int
  | 0, ts => ([], ts)
  | n+1, (c :: w :: ts) => let r := takePairs n ts; (((c : F), w.toNat) :: r.1, r.2)
  | _+1, ts => ([], ts)

/-- Decode a flat token stream `nL c w … nR c w … nO c w …` per constraint into `cs`. Fuel = the
constraint count (emitted alongside), so the recursion is structural and total. -/
def parseCons : ℕ → List Int → List (R1CSChecker.Con F)
  | 0, _ => []
  | fuel+1, (nl :: rest) =>
      let rL := takePairs nl.toNat rest
      match rL.2 with
      | (nr :: rest2) =>
          let rR := takePairs nr.toNat rest2
          match rR.2 with
          | (no :: rest3) =>
              let rO := takePairs no.toNat rest3
              (⟨rL.1, rR.1, rO.1⟩ : R1CSChecker.Con F) :: parseCons fuel rO.2
          | [] => []
      | [] => []
  | _+1, [] => []

/-- Read `n` wire indices off the token stream. -/
def takeNats : ℕ → List Int → List ℕ × List Int
  | 0, ts => ([], ts)
  | n+1, (w :: ts) => let r := takeNats n ts; (w.toNat :: r.1, r.2)
  | _+1, [] => ([], [])

/-- Decode the bit groups: per group `nBits b… nVal c w …`. Fuel = the group count. -/
def parseGroups : ℕ → List Int → List (List ℕ × List (F × ℕ))
  | 0, _ => []
  | fuel+1, (nb :: rest) =>
      let rb := takeNats nb.toNat rest
      match rb.2 with
      | (nv :: rest2) => let rv := takePairs nv.toNat rest2; (rb.1, rv.1) :: parseGroups fuel rv.2
      | [] => []
  | _+1, [] => []

end Parse

end R1CSChecker
