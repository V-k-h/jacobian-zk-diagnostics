/-
RedundancyCert.lean — the differential step of the paper's local-redundancy
certificate (ePrint 2026/1852, Lemma "Local-redundancy certificate").

The paper discards a vacuous constraint row `g` from the augmented Jacobian
when an explicit identity  w * g = ∑ i, q i * f i  holds with the retained
constraints `f i` and a multiplier `w` that does not vanish at the witness.
The proof's differential step — differentiate the identity, evaluate at a
satisfying point, and conclude that the dropped row's gradient lies in the
span of the retained rows' gradients — is formalised here, kernel-checked:

  `redundant_row_differential` :
      w * g = ∑ i in s, q i * f i   →   eval a g = 0   →  (∀ i ∈ s, eval a (f i) = 0)
      →  eval a w * eval a (pderiv j g)
           = ∑ i in s, eval a (q i) * eval a (pderiv j (f i))

With `eval a w ≠ 0` (the certificate's side condition) this exhibits each
coordinate of the dropped row as the fixed linear combination
(eval a (q i) / eval a w) of the retained rows — the exact sentence used in
the paper's proof. Krull-height smoothness and Lang–Weil counting are not
formalised; this file covers only the identity-to-row-span step, in the same
complementary spirit as R1CSChecker.lean.

No `sorry`; standard axioms only. Check in place:
    cd lean && lake env lean RedundancyCert.lean
-/
import Mathlib

open MvPolynomial

variable {σ R ι : Type*} [CommRing R]

/-- Differentiating a redundancy identity `w * g = ∑ q i * f i` and evaluating
at a common zero `a` of `g` and every `f i` kills the product-rule cross terms,
leaving the dropped row's gradient as an explicit combination of the retained
gradients. -/
theorem redundant_row_differential
    (w g : MvPolynomial σ R) (s : Finset ι) (q f : ι → MvPolynomial σ R)
    (hid : w * g = ∑ i ∈ s, q i * f i)
    (a : σ → R) (hg : eval a g = 0) (hf : ∀ i ∈ s, eval a (f i) = 0) (j : σ) :
    eval a w * eval a (pderiv j g)
      = ∑ i ∈ s, eval a (q i) * eval a (pderiv j (f i)) := by
  have hD : pderiv j (w * g) = pderiv j (∑ i ∈ s, q i * f i) := congrArg _ hid
  rw [pderiv_mul, map_sum] at hD
  have hE := congrArg (eval a) hD
  rw [map_add, map_mul, map_mul, map_sum] at hE
  simp only [pderiv_mul, map_add, map_mul, hg, mul_zero, zero_add] at hE
  -- cross terms are gone on the left (g(a) = 0); kill them on the right
  rw [hE]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hf i hi, mul_zero, zero_add]

/-- The certificate's conclusion in row form: when the multiplier is a unit at
the witness, every coordinate of the dropped row equals a fixed linear
combination of the retained rows' coordinates, with coefficients independent
of the coordinate `j` — i.e. the dropped row lies in their span. -/
theorem redundant_row_in_span
    {F : Type*} [Field F]
    (w g : MvPolynomial σ F) (s : Finset ι) (q f : ι → MvPolynomial σ F)
    (hid : w * g = ∑ i ∈ s, q i * f i)
    (a : σ → F) (hg : eval a g = 0) (hf : ∀ i ∈ s, eval a (f i) = 0)
    (hw : eval a w ≠ 0) (j : σ) :
    eval a (pderiv j g)
      = ∑ i ∈ s, (eval a (q i) / eval a w) * eval a (pderiv j (f i)) := by
  have h := redundant_row_differential w g s q f hid a hg hf j
  have hsum : ∑ i ∈ s, (eval a (q i) / eval a w) * eval a (pderiv j (f i))
      = (∑ i ∈ s, eval a (q i) * eval a (pderiv j (f i))) / eval a w := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => (div_mul_eq_mul_div _ _ _).trans rfl
  rw [hsum, eq_div_iff hw, mul_comm]
  exact h

/-- Sanity instance mirroring the paper's reproducer: the identity
`(s-1)·[s(y-u)] = (y-u)·[s(s-1)]` discharges a verification row against the
retained booleanity row. Stated over any commutative ring. -/
example (sv yv uv : MvPolynomial (Fin 3) ℤ)
    (hs : sv = X 0) (hy : yv = X 1) (hu : uv = X 2) :
    (sv - 1) * (sv * (yv - uv)) = (yv - uv) * (sv * (sv - 1)) := by
  subst hs hy hu; ring
