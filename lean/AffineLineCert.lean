/-
AffineLineCert.lean — the algebraic core of the affine-line certificate
(ePrint 2026/1852, Proposition "Affine-line certificate").

An R1CS row is f(x) = (L x + lc)(R x + rc) − (O x + oc) with L, R, O linear.
The certificate rests on the exact quadratic expansion along a line
a + t•v, whose t² coefficient is (L v)(R v): if the row vanishes at a, the
directional derivative vanishes, and (L v)(R v) = 0, then the row vanishes
at every point of the line — and conversely, under the first two
hypotheses, vanishing at the single point a + v already forces
(L v)(R v) = 0. Both directions are kernel-checked here over an arbitrary
commutative ring, so the result is characteristic-free, exactly as the
paper states. The bookkeeping that v fixes the conditioned coordinates
(v_F = 0) is a coordinate statement outside this algebraic core.

No `sorry`; standard axioms only. Check in place:
    cd lean && lake env lean AffineLineCert.lean
-/
import Mathlib

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- An R1CS row: bilinear product of two affine forms minus a third. -/
def r1csRow (L Rf O : V →ₗ[R] R) (lc rc oc : R) (x : V) : R :=
  (L x + lc) * (Rf x + rc) - (O x + oc)

/-- Exact quadratic expansion of a row along the line `a + t • v`. -/
theorem r1csRow_line_expansion (L Rf O : V →ₗ[R] R) (lc rc oc : R) (a v : V) (t : R) :
    r1csRow L Rf O lc rc oc (a + t • v)
      = r1csRow L Rf O lc rc oc a
        + t * (L v * (Rf a + rc) + (L a + lc) * Rf v - O v)
        + t ^ 2 * (L v * Rf v) := by
  simp only [r1csRow, map_add, map_smul, smul_eq_mul]
  ring

/-- Affine-line certificate, forward direction: a satisfying point, a tangent
direction, and a vanishing quadratic directional coefficient put the whole
line inside the row's zero set. -/
theorem r1csRow_vanishes_on_line (L Rf O : V →ₗ[R] R) (lc rc oc : R) (a v : V)
    (h0 : r1csRow L Rf O lc rc oc a = 0)
    (h1 : L v * (Rf a + rc) + (L a + lc) * Rf v - O v = 0)
    (h2 : L v * Rf v = 0) (t : R) :
    r1csRow L Rf O lc rc oc (a + t • v) = 0 := by
  rw [r1csRow_line_expansion, h0, h1, h2]
  ring

/-- Converse: under the satisfaction and tangency hypotheses, vanishing at the
single point `a + v` already forces the quadratic directional coefficient to
vanish — so the three-coefficient check is equivalent to satisfaction along
the entire line. -/
theorem quadratic_coefficient_of_point (L Rf O : V →ₗ[R] R) (lc rc oc : R) (a v : V)
    (h0 : r1csRow L Rf O lc rc oc a = 0)
    (h1 : L v * (Rf a + rc) + (L a + lc) * Rf v - O v = 0)
    (hp : r1csRow L Rf O lc rc oc (a + v) = 0) :
    L v * Rf v = 0 := by
  have h := r1csRow_line_expansion L Rf O lc rc oc a v 1
  rw [one_smul, hp, h0, h1] at h
  linear_combination -h

/-- Exact quartic expansion of a row along the parabola `a + t • v + t^2 • u`:
the degree-`k` coefficients are the certificate conditions of the
affine-parabola certificate (ePrint 2026/1852, Theorem "Affine-parabola
certificate"). -/
theorem r1csRow_parabola_expansion (L Rf O : V →ₗ[R] R) (lc rc oc : R) (a v u : V) (t : R) :
    r1csRow L Rf O lc rc oc (a + t • v + t ^ 2 • u)
      = r1csRow L Rf O lc rc oc a
        + t * (L v * (Rf a + rc) + (L a + lc) * Rf v - O v)
        + t ^ 2 * ((L u * (Rf a + rc) + (L a + lc) * Rf u - O u) + L v * Rf v)
        + t ^ 3 * (L v * Rf u + L u * Rf v)
        + t ^ 4 * (L u * Rf u) := by
  simp only [r1csRow, map_add, map_smul, smul_eq_mul]
  ring

/-- Affine-parabola certificate, forward direction: a satisfying point, a
tangent direction `v`, a correction `u` solving the second- and third-order
conditions, and a vanishing quartic coefficient put the whole parabola inside
the row's zero set, in every characteristic. -/
theorem r1csRow_vanishes_on_parabola (L Rf O : V →ₗ[R] R) (lc rc oc : R) (a v u : V)
    (h0 : r1csRow L Rf O lc rc oc a = 0)
    (h1 : L v * (Rf a + rc) + (L a + lc) * Rf v - O v = 0)
    (h2 : (L u * (Rf a + rc) + (L a + lc) * Rf u - O u) + L v * Rf v = 0)
    (h3 : L v * Rf u + L u * Rf v = 0)
    (h4 : L u * Rf u = 0) (t : R) :
    r1csRow L Rf O lc rc oc (a + t • v + t ^ 2 • u) = 0 := by
  rw [r1csRow_parabola_expansion, h0, h1, h2, h3, h4]
  ring

/-- Target movement: along a certified line over a field, a coordinate the
direction moves takes every field value exactly once; specialised here to the
value map `t ↦ c a + t * c v` for a coordinate functional `c`. -/
theorem target_attains_all_values {F W : Type*} [Field F] [AddCommGroup W] [Module F W]
    (c : W →ₗ[F] F) (a v : W) (hv : c v ≠ 0) :
    Function.Bijective fun t : F => c (a + t • v) := by
  have : (fun t : F => c (a + t • v)) = fun t => c a + t * c v := by
    funext t; simp [map_add, map_smul, smul_eq_mul]
  rw [this]
  constructor
  · intro s t hst
    have := add_left_cancel hst
    exact mul_right_cancel₀ hv this
  · intro y
    exact ⟨(y - c a) / c v, by field_simp⟩
