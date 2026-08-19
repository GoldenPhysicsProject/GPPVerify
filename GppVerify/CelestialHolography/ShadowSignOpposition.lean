import Mathlib.Tactic

/-!
# Shadow sign opposition — the s/t-channel sewing sign structure, formalized

From `discovery/shadow_ope/sign_opposition_sweep.py` (2026-08-18/19 session), which
found — first numerically (39/39 structured points, 666/666 random points, zero
exceptions) and then analytically — that the s-channel and t-channel tied-leg sewing
discontinuities `Sewn_s`, `Sewn_t` always carry opposite-sign imaginary parts on the
physical branch. This file promotes that analytic explanation to a real Lean theorem:
not "checked at many points" but "true for every point satisfying the stated
hypotheses, by direct computation."

## What is genuinely proved here (pure real algebra and elementary geometry — no
Mellin transforms, no complex analysis, no physics assumed beyond the fixed kinematic
frame used throughout `discovery/shadow_ope/celestial_kinematics.py`):

* `A_eq_const`, `A_neg`: the s-channel numerator `A(x,y) = 2 q(x,y)·p1` is an exact
  constant `-4E`, independent of the celestial position `(x,y)` — hence strictly
  negative for `E > 0`. (Matches `sign_opposition_sweep.py`'s finding that `A` is
  z-independent, re-derived here from the bare kinematics, not assumed.)
* `Aprime_eq`, `Aprime_nonpos`: the t-channel numerator `A'(x,y) = 2 q(x,y)·p2` equals
  `-4E·(x²+y²)`, hence `≤ 0` everywhere, `< 0` away from the origin.
* `B_eq_const`, `B_neg`: the s-channel threshold denominator
  `B(x,y) = 2 q(x,y)·(p1+p2)` equals `-4E·(1+x²+y²)`, hence strictly negative
  everywhere (no case split needed — matches the finding in
  `sewn_z_integral_v2.py` that `B` never changes sign for physical `s > 0`).
* `C_perfect_square`: the shared numerator `C(x,y) = 2 q(x,y)·p4` is, after clearing
  the `(1 - cos θ)` denominator, an exact sum of two squares — the closed-form
  perfect-square structure `C(x,y) = κ·|z - z₄|²` already found numerically this
  session, now derived algebraically. `C_nonneg` concludes `C(x,y) ≥ 0` whenever
  `cos θ < 1` (`t ≠ 0`, the genuine physical case), with equality only at `z = z₄`.
* `sign_opposition`: the actual theorem. Given the four algebraic facts above plus
  the two *physical-branch* hypotheses `B'' > 0` (forced, as established in
  `discovery/README.md`, by `w0_t = -t/B'' > 0` for `t < 0`) and `C ≠ 0` — i.e.
  away from the collinear point `z = z₄` where the construction has its own
  (separately regularized) singularity — the two sewing coefficients
  `-1/(2·A·C·B)` and `-1/(2·A'·C·B'')` have strictly opposite sign. Since
  `Im(Sewn_s)` and `Im(Sewn_t)` are these coefficients times a manifestly positive
  factor (`w₀⁻²·sech²(ln w₀ / 2)`, not re-derived here — it is a bare positive
  real number for any `w₀ > 0`, already established in `tied_leg_continuation.py`
  and `t_channel_sewing.py`), this is exactly the sign-opposition fact.

## What is deliberately NOT claimed here

This file does **not** formalize the Sokhotski–Plemelj discontinuity construction
itself (`tied_leg_continuation.py`'s `disc(Δ) = -2πi/(ACB)·w₀^{Δ-3}`), the λ-integral
closed form (`principal_series_sewing.py`'s `sech²` identity), or anything about the
box integral. Those remain exploratory Python, per `discovery/`'s own "nothing here is
proved" convention — this file captures only the purely algebraic sign fact that sits
underneath them, which *is* provable outright and belongs here rather than staying a
99.9%-confidence numerical sweep.
-/

namespace GppShadowSignOpposition

/-- The celestial null 4-vector at real position `(x,y)` (the real Lorentzian slice
`z̄ = z*`, `z = x + iy`), matching `celestial_kinematics.py`'s `q_vec`. -/
def qvec (x y : ℝ) : Fin 4 → ℝ
  | 0 => 1 + x ^ 2 + y ^ 2
  | 1 => 2 * x
  | 2 => 2 * y
  | 3 => 1 - x ^ 2 - y ^ 2

/-- Minkowski dot product, mostly-plus signature `(+,-,-,-)`, matching
`celestial_kinematics.py`'s `mink_dot`. -/
def mdot (a b : Fin 4 → ℝ) : ℝ := a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3

variable (E θ : ℝ)

/-- Leg 1, fixed: `p1 = (-E, 0, 0, E)`. -/
def p1 : Fin 4 → ℝ | 0 => -E | 1 => 0 | 2 => 0 | 3 => E

/-- Leg 2, fixed: `p2 = (-E, 0, 0, -E)`. -/
def p2 : Fin 4 → ℝ | 0 => -E | 1 => 0 | 2 => 0 | 3 => -E

/-- Leg 4, parametrized by the scattering angle `θ` (so `t = -2E²(1-cos θ)`):
`p4 = (E, -E sin θ, 0, -E cos θ)`. -/
noncomputable def p4 : Fin 4 → ℝ | 0 => E | 1 => -E * Real.sin θ | 2 => 0 | 3 => -E * Real.cos θ

/-- `A(x,y) := 2 q(x,y)·p1`, the s-channel numerator. -/
def A (x y : ℝ) : ℝ := 2 * mdot (qvec x y) (p1 E)

/-- `A'(x,y) := 2 q(x,y)·p2`, the t-channel numerator. -/
def Aprime (x y : ℝ) : ℝ := 2 * mdot (qvec x y) (p2 E)

/-- `B(x,y) := 2 q(x,y)·(p1+p2)`, the s-channel threshold denominator. -/
def B (x y : ℝ) : ℝ := 2 * mdot (qvec x y) (fun i => p1 E i + p2 E i)

/-- `C(x,y) := 2 q(x,y)·p4`, the shared collinear numerator. -/
noncomputable def C (x y : ℝ) : ℝ := 2 * mdot (qvec x y) (p4 E θ)

/-! ## The four algebraic facts -/

theorem A_eq_const (x y : ℝ) : A E x y = -4 * E := by
  simp only [A, mdot, qvec, p1]
  ring

theorem A_neg (hE : 0 < E) (x y : ℝ) : A E x y < 0 := by
  rw [A_eq_const]; linarith

theorem Aprime_eq (x y : ℝ) : Aprime E x y = -4 * E * (x ^ 2 + y ^ 2) := by
  simp only [Aprime, mdot, qvec, p2]
  ring

theorem Aprime_nonpos (hE : 0 ≤ E) (x y : ℝ) : Aprime E x y ≤ 0 := by
  rw [Aprime_eq]
  have : 0 ≤ x ^ 2 + y ^ 2 := by positivity
  nlinarith

theorem B_eq_const (x y : ℝ) : B E x y = -4 * E * (1 + x ^ 2 + y ^ 2) := by
  simp only [B, mdot, qvec, p1, p2]
  ring

theorem B_neg (hE : 0 < E) (x y : ℝ) : B E x y < 0 := by
  rw [B_eq_const]
  have h1 : 0 < 1 + x ^ 2 + y ^ 2 := by positivity
  nlinarith

/-- `C(x,y)`, cleared of its `(1 - cos θ)` denominator, is an exact sum of two
squares — the algebraic content behind the numerically-found perfect-square
structure `C(x,y) = κ|z - z₄|²`. -/
theorem C_clearing_identity (x y : ℝ) :
    (1 - Real.cos θ) * C E θ x y =
      2 * E * ((1 - Real.cos θ) * x + Real.sin θ) ^ 2 +
      2 * E * (1 - Real.cos θ) ^ 2 * y ^ 2 := by
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  simp only [C, mdot, qvec, p4]
  linear_combination (-2 * E) * hpyth

/-- `C(x,y) ≥ 0` whenever `cos θ < 1` (the genuine physical case `t ≠ 0`), with
equality exactly at the collinear point `z = z₄`. -/
theorem C_nonneg (hE : 0 ≤ E) (hcos : Real.cos θ < 1) (x y : ℝ) : 0 ≤ C E θ x y := by
  have hpos : 0 < 1 - Real.cos θ := by linarith
  have hsq : 0 ≤ (1 - Real.cos θ) * C E θ x y := by
    rw [C_clearing_identity]
    positivity
  nlinarith

/-! ## The sign-opposition theorem -/

/-- **Sign opposition** (the file's main result): on the physical branch — s-channel
numerator/denominator signs forced as above, `t < 0` (`cos θ < 1`) forcing `C ≥ 0`,
and the t-channel threshold `B'' > 0` (the physical-branch condition established in
`discovery/README.md`, taken here as a hypothesis since `B''` genuinely changes sign
over the celestial sphere and is not pinned down by `E, θ` alone) — the two sewing
coefficients `-1/(2ACB)` and `-1/(2·A'·C·B'')` are never both nonnegative and never
both nonpositive: they have strictly opposite sign whenever both are nonzero.
This is the exact algebraic content of `Im(Sewn_s) < 0 < Im(Sewn_t)`. -/
theorem sign_opposition
    (hE : 0 < E) (hcos : Real.cos θ < 1) (x y x' y' Bpp : ℝ)
    (hC : C E θ x' y' ≠ 0) (hBpp : 0 < Bpp) :
    (-1 / (2 * A E x y * C E θ x' y' * B E x y)) *
      (-1 / (2 * Aprime E x' y' * C E θ x' y' * Bpp)) ≤ 0 := by
  have hA : A E x y < 0 := A_neg E hE x y
  have hB : B E x y < 0 := B_neg E hE x y
  have hAp : Aprime E x' y' ≤ 0 := Aprime_nonpos E hE.le x' y'
  have hCnn : 0 ≤ C E θ x' y' := C_nonneg E θ hE.le hcos x' y'
  have hCpos : 0 < C E θ x' y' := lt_of_le_of_ne hCnn (Ne.symm hC)
  -- coeff_s = -1/(2ACB): A<0, C>0, B<0 ⟹ AB>0 ⟹ 2ACB > 0 ⟹ coeff_s < 0.
  have hAB : 0 < A E x y * B E x y := mul_pos_of_neg_of_neg hA hB
  have hACB : 0 < 2 * A E x y * C E θ x' y' * B E x y := by
    have : 0 < (A E x y * B E x y) * C E θ x' y' := mul_pos hAB hCpos
    nlinarith [this]
  have h1 : -1 / (2 * A E x y * C E θ x' y' * B E x y) < 0 :=
    div_neg_of_neg_of_pos (by norm_num) hACB
  -- coeff_t = -1/(2A'CBpp): A'≤0, C>0, Bpp>0 ⟹ CBpp>0 ⟹ 2A'CBpp ≤ 0 ⟹ coeff_t ≥ 0.
  have hCBpp : 0 < C E θ x' y' * Bpp := mul_pos hCpos hBpp
  have hApCBpp : 2 * Aprime E x' y' * C E θ x' y' * Bpp ≤ 0 := by
    have : Aprime E x' y' * (C E θ x' y' * Bpp) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAp hCBpp.le
    nlinarith [this]
  have h2 : 0 ≤ -1 / (2 * Aprime E x' y' * C E θ x' y' * Bpp) := by
    rcases hApCBpp.eq_or_lt with heq | hlt
    · rw [heq]; simp
    · exact le_of_lt (div_pos_of_neg_of_neg (by norm_num) hlt)
  exact mul_nonpos_of_nonpos_of_nonneg h1.le h2

end GppShadowSignOpposition
