import Mathlib

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

-- ── inlined verified checker (lean/R1CSChecker.lean) ──
namespace R1CSChecker

variable {F : Type*} [CommRing F]

/-- Evaluate a sparse linear form `Σ cᵢ·a(wᵢ)`. -/
def dotp (l : List (F × ℕ)) (a : ℕ → F) : F := (l.map fun t => t.1 * a t.2).sum

@[simp] theorem dotp_cons (t : F × ℕ) (l : List (F × ℕ)) (a : ℕ → F) :
    dotp (t :: l) a = t.1 * a t.2 + dotp l a := rfl

/-- An R1CS constraint `(L·a)(R·a) = (O·a)`. -/
structure Con (F : Type*) where
  L : List (F × ℕ)
  R : List (F × ℕ)
  O : List (F × ℕ)

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

end R1CSChecker
-- ── end inlined checker ──

/- Scalable determinacy certificate (5 wires, 3 constraints). -/
namespace GnarkCheckDemo

abbrev p : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

def cs : List (R1CSChecker.Con (ZMod p)) := [
  ⟨[((1 : ZMod p), 1)], [((1 : ZMod p), 1)], [((1 : ZMod p), 2)]⟩,
  ⟨[((1 : ZMod p), 2)], [((1 : ZMod p), 1)], [((1 : ZMod p), 3)]⟩,
  ⟨[((1 : ZMod p), 3), ((1 : ZMod p), 1)], [((1 : ZMod p), 0)], [((1 : ZMod p), 4)]⟩
]

def I : List ℕ := [0, 1]

/-- Determinacy, one line: any two satisfying assignments agreeing on the inputs agree on
    every wire the checker determines. The field reasoning is `R1CSChecker.fold_sound`. -/
theorem determined : ∀ {a a' : ℕ → ZMod p}, R1CSChecker.sat cs a → R1CSChecker.sat cs a' →
    R1CSChecker.agree I a a' → R1CSChecker.agree (cs.foldl R1CSChecker.stepPin I) a a' :=
  R1CSChecker.fold_sound cs I

/-- The checker determines all 3 functionally-pinned wires (verified by reduction). -/
example : [2, 3, 4].all (fun w => (cs.foldl R1CSChecker.stepPin I).contains w) = true :=
  by native_decide

end GnarkCheckDemo
