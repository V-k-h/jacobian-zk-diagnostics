import Mathlib

/-!
# Multiplicity bounds from degree — the keystone for constraint systems beyond R1CS

The existing leaf rules discharge a wire when it appears **linearly** in a constraint:
`Composition.detBy_linpin` and `GnarkR1CS.r1cs_funpin` both need the wire to be
isolable as `c·w + rest` with `c ≠ 0`. That is the whole of what R1CS can present,
because `(L·a)(R·a) = O·a` is degree 2 overall and any single wire appears at degree
≤ 2 — and at degree 2 only as a square on one side, which the detector declines.

Plonkish relations are not so bounded. Poseidon2's S-box is `s⁵`, the elliptic
identities reach degree 6, and the delta-range constraint is a genuine quartic
`d(d−1)(d−2)(d−3)`. A wire appearing at degree `d > 1` is **not** determined, but
neither is it unconstrained: it has at most `d` admissible values. That distinction is
exactly what the engine's C1 gate needs, and it is the fact this file supplies.

## Why this is the keystone theorem

`compose/polysys.py::step_degree_poly` computes `deg_w(g)` together with the leading
coefficient, and `gnark_audit`'s C1 gate consumes the result three ways:

* bound `= 1` — the wire is determined (already covered by `detBy_linpin`);
* bound `> 1` — the wire is **provably multi-valued**, so C1 *fails*. A flattened
  quartic defeated an earlier version of that gate precisely here: it is first-order
  determined at a simple root yet has four satisfying values, and the gate reported
  SAFE. Refuting uniqueness needs a real upper bound, not the absence of a pin;
* bound `= None` — declined, which now also fails rather than being filtered out.

So the engine is already reasoning "at most `d` values". Until now that step was a
Python argument. `card_values_le_degree` below makes it a theorem, which is what lets
the Plonkish path rest on the same kernel as the R1CS path.

## The lookup corollary

A lookup `∃ j, w = table j` is disjunctive and cannot be written as a vanishing
polynomial, so it looks like it falls outside this framework. It does not: a lookup
against a table of `n` entries bounds `w` to `n` values, which is the same shape of
fact — see `card_values_le_of_mem_image`. Lookups therefore *constrain without
pinning*, and they compose with the degree bounds through the same C1 gate rather
than needing separate machinery.

## Statement shape

Everything is relative to a reference assignment `a₀` and the set `S` of already-pinned
variables, matching `Slocal` in `GnarkR1CS`: the coefficients may depend on the
assignment, but only through `S`. The conclusion bounds the number of distinct values
`w` takes across satisfying assignments that agree with `a₀` on `S` — which is the
two-run/multi-run quantity the whole development is phrased in.
-/

-- `card_values_le_of_mem_image` and `subsingleton_of_bound_one` are pure cardinality
-- facts and do not use `[Field F]`; they live here because they feed the same C1 gate.
set_option linter.unusedSectionVars false

namespace Multiplicity

open Polynomial

variable {Var F : Type*}

/-- Two assignments agree on a set of variables (as in `Composition`). -/
def agree (S : Set Var) (a a' : Var → F) : Prop := ∀ v ∈ S, a v = a' v

/-- A scalar read of the assignment depends only on the variables in `S`
(as in `GnarkR1CS`). -/
def Slocal (S : Set Var) (g : (Var → F) → F) : Prop :=
  ∀ a a', agree S a a' → g a = g a'

variable [Field F] {sat : (Var → F) → Prop}

/-- The values a wire takes over satisfying assignments that agree with `a₀` on `S`. -/
def valueSet (sat : (Var → F) → Prop) (S : Set Var) (a₀ : Var → F) (w : Var) : Set F :=
  {v | ∃ a, sat a ∧ agree S a₀ a ∧ a w = v}

/-- The polynomial the constraint presents in `w` once every other variable is fixed by
`S`. Coefficients are read at the reference assignment; `Slocal` is what makes that
legitimate. -/
noncomputable def coeffPoly (c : ℕ → (Var → F) → F) (a₀ : Var → F) (d : ℕ) : F[X] :=
  ∑ k ∈ Finset.range (d + 1), Polynomial.C (c k a₀) * X ^ k

lemma coeffPoly_eval (c : ℕ → (Var → F) → F) (a₀ : Var → F) (d : ℕ) (v : F) :
    (coeffPoly c a₀ d).eval v = ∑ k ∈ Finset.range (d + 1), c k a₀ * v ^ k := by
  simp [coeffPoly, eval_finset_sum]

lemma coeffPoly_natDegree_le (c : ℕ → (Var → F) → F) (a₀ : Var → F) (d : ℕ) :
    (coeffPoly c a₀ d).natDegree ≤ d := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  calc (Polynomial.C (c k a₀) * X ^ k).natDegree
      ≤ ((X : F[X]) ^ k).natDegree := natDegree_C_mul_le (c k a₀) (X ^ k)
    _ = k := natDegree_X_pow k
    _ ≤ d := hk'

lemma coeffPoly_coeff_top (c : ℕ → (Var → F) → F) (a₀ : Var → F) (d : ℕ) :
    (coeffPoly c a₀ d).coeff d = c d a₀ := by
  simp [coeffPoly, finset_sum_coeff, coeff_C_mul, coeff_X_pow]

lemma coeffPoly_ne_zero {c : ℕ → (Var → F) → F} {a₀ : Var → F} {d : ℕ}
    (hlead : c d a₀ ≠ 0) : coeffPoly c a₀ d ≠ 0 := fun h => by
  apply hlead
  rw [← coeffPoly_coeff_top c a₀ d, h, coeff_zero]

/-- **The multiplicity bound.** If a constraint presents `w` as a degree-`d` polynomial
whose coefficients depend on the assignment only through `S`, and whose leading
coefficient is nonzero at the reference assignment, then `w` takes at most `d` distinct
values across satisfying assignments agreeing with `a₀` on `S`.

This is the generalisation of the linear leaf rules to arbitrary degree: at `d = 1` the
value set is a singleton, recovering determinacy (`card_le_one_iff` below); at `d > 1`
it is the upper bound that lets a uniqueness claim be *refuted* rather than merely left
unproven. -/
theorem card_values_le_degree {S : Set Var} {w : Var} {d : ℕ}
    {c : ℕ → (Var → F) → F} {a₀ : Var → F}
    (hloc : ∀ k, Slocal S (c k))
    (hlead : c d a₀ ≠ 0)
    (hcon : ∀ a, sat a → agree S a₀ a →
      ∑ k ∈ Finset.range (d + 1), c k a * (a w) ^ k = 0) :
    (valueSet sat S a₀ w).Finite ∧ (valueSet sat S a₀ w).ncard ≤ d := by
  set P := coeffPoly c a₀ d with hP
  have hPne : P ≠ 0 := coeffPoly_ne_zero hlead
  -- every attainable value is a root of `P`: the coefficients are `S`-local, so they
  -- read the same at `a` as at the reference `a₀`
  have hroot : ∀ v ∈ valueSet sat S a₀ w, P.IsRoot v := by
    rintro v ⟨a, hsa, hag, rfl⟩
    have hz : ∑ k ∈ Finset.range (d + 1), c k a₀ * (a w) ^ k = 0 := by
      have h := hcon a hsa hag
      have hc : ∀ k, c k a = c k a₀ := fun k => (hloc k a₀ a hag).symm
      simpa [hc] using h
    show P.eval (a w) = 0
    rw [hP, coeffPoly_eval]; exact hz
  have hfin : (valueSet sat S a₀ w).Finite :=
    Set.Finite.subset (finite_setOf_isRoot hPne) hroot
  refine ⟨hfin, ?_⟩
  -- push the value set through `card_le_degree_of_subset_roots`
  have hZ : hfin.toFinset.val ⊆ P.roots := by
    intro v hv
    have hv' : v ∈ valueSet sat S a₀ w := by
      rwa [← Set.Finite.mem_toFinset hfin, ← Finset.mem_val]
    exact mem_roots'.mpr ⟨hPne, hroot v hv'⟩
  calc (valueSet sat S a₀ w).ncard = hfin.toFinset.card := Set.ncard_eq_toFinset_card _ hfin
    _ ≤ P.natDegree := card_le_degree_of_subset_roots hZ
    _ ≤ d := coeffPoly_natDegree_le c a₀ d

/-- **Lookup corollary.** A wire constrained to lie in the image of a finite index type
takes at most `Fintype.card ι` values. Nothing about the table is assumed beyond
finiteness — in particular the entries need not be distinct, so this is an upper bound
on a lookup's multiplicity exactly as `card_values_le_degree` is on a polynomial gate.
Lookups therefore feed the same C1 gate rather than requiring separate machinery. -/
theorem card_values_le_of_mem_image {S : Set Var} {w : Var} {ι : Type*} [Fintype ι]
    {table : ι → F} {a₀ : Var → F}
    (hcon : ∀ a, sat a → agree S a₀ a → ∃ j : ι, a w = table j) :
    (valueSet sat S a₀ w).Finite ∧
      (valueSet sat S a₀ w).ncard ≤ Fintype.card ι := by
  have hsub : valueSet sat S a₀ w ⊆ Set.range table := by
    rintro v ⟨a, hsa, hag, rfl⟩
    obtain ⟨j, hj⟩ := hcon a hsa hag
    exact ⟨j, hj.symm⟩
  have hfin : (valueSet sat S a₀ w).Finite :=
    Set.Finite.subset (Set.finite_range table) hsub
  refine ⟨hfin, ?_⟩
  classical
  have hrange : Set.range table = ↑(Finset.univ.image table) := by ext x; simp
  calc (valueSet sat S a₀ w).ncard ≤ (Set.range table).ncard :=
        Set.ncard_le_ncard hsub (Set.finite_range table)
    _ = (Finset.univ.image table).card := by rw [hrange, Set.ncard_coe_Finset]
    _ ≤ (Finset.univ : Finset ι).card := Finset.card_image_le
    _ = Fintype.card ι := Finset.card_univ

/-- At `d = 1` the bound collapses to determinacy, so the linear leaf rules are the
degree-1 instance of `card_values_le_degree` rather than a separate family. Stated on
the value set to keep it independent of any particular `DetBy` restatement. -/
theorem subsingleton_of_bound_one {S : Set Var} {w : Var} {a₀ : Var → F}
    (h : (valueSet sat S a₀ w).Finite ∧ (valueSet sat S a₀ w).ncard ≤ 1) :
    ∀ v ∈ valueSet sat S a₀ w, ∀ v' ∈ valueSet sat S a₀ w, v = v' := by
  exact (Set.ncard_le_one h.1).mp h.2

end Multiplicity

/-! ## Proof-core hygiene

No `sorry` and no local axiom: the only axioms below are Lean's three standard ones
(`propext`, `Classical.choice`, `Quot.sound`), which Mathlib itself rests on. -/

#print axioms Multiplicity.card_values_le_degree
#print axioms Multiplicity.card_values_le_of_mem_image
#print axioms Multiplicity.subsingleton_of_bound_one
