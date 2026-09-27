import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# Raised-box simplex: scaled Beta integral layer

This file formalizes the one-dimensional Beta identities used in the exact
three-simplex majorant reduction.  It does not yet assert the full nested
simplex integral or dominated-convergence theorem.

For `0 < δ < 1` and `a > 0`, the inner integral occurring after integrating the
spectator simplex coordinate has the complex-power form

  ∫_0^a x^{-δ} (a-x) dx
    = a^(2-δ) B(1-δ,2).

A second unit-interval Beta factor is `B(1-δ,3-δ)`.  The positivity statements
below certify exactly the convergence hypotheses required by Mathlib's Beta
integral theorems.
-/

namespace GppRaisedBoxSimplexBetaLayer

open Complex
open scoped Interval

/-- The first Beta parameter `1-δ` lies in the convergent half-plane when
`δ < 1`. -/
theorem one_sub_delta_re_pos {δ : ℝ} (hδ : δ < 1) :
    0 < (((1 - δ : ℝ) : ℂ)).re := by
  simpa using sub_pos.mpr hδ

/-- The second outer Beta parameter `3-δ` is positive on `0 < δ < 1`. -/
theorem three_sub_delta_re_pos {δ : ℝ} (hδ : δ < 1) :
    0 < (((3 - δ : ℝ) : ℂ)).re := by
  simp
  linarith

/-- Exact scaled Beta identity for the inner raised-box majorant integral. -/
theorem inner_scaled_beta_identity
    {δ a : ℝ} (ha : 0 < a) :
    (∫ x in (0)..a,
      (x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
        ((a : ℂ) - x) ^ (((2 : ℂ) - 1))) =
      (a : ℂ) ^ ((((1 - δ : ℝ) : ℂ) + 2 - 1)) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2 := by
  simpa using
    (betaIntegral_scaled (((1 - δ : ℝ) : ℂ)) (2 : ℂ) ha)

/-- A reusable integrability companion to Mathlib's `betaIntegral_scaled`.
Mathlib proves the value of the scaled interval integral but does not separately
expose its `IntervalIntegrable` certificate.  We obtain it from the unit Beta
kernel by the affine rescaling `u = x / a`; endpoint values are irrelevant for
Lebesgue interval integrability. -/
theorem scaled_beta_convergent
    {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) {a : ℝ} (ha : 0 < a) :
    IntervalIntegrable
      (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) * (((a : ℂ) - x) ^ (t - 1)))
      MeasureTheory.volume 0 a := by
  let f : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (s - 1) * (1 - (u : ℂ)) ^ (t - 1)
  have hf : IntervalIntegrable f MeasureTheory.volume 0 1 := by
    simpa [f] using betaIntegral_convergent hs ht
  have ha0 : a ≠ 0 := ha.ne'
  have hscaled :
      IntervalIntegrable (fun x : ℝ => f (x / a)) MeasureTheory.volume 0 a := by
    have h := hf.comp_mul_left (c := a⁻¹)
    simpa [div_eq_mul_inv, ha0, f, mul_comm, mul_left_comm, mul_assoc] using h
  have hconst := hscaled.const_mul
    (((a : ℂ) ^ (s - 1)) * ((a : ℂ) ^ (t - 1)))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ha.le] at hconst ⊢
  refine hconst.congr_fun ?_ measurableSet_Ioo
  intro x hx
  have hxa : 0 < x / a := div_pos hx.1 ha
  have hxa1 : x / a < 1 := (div_lt_one ha).2 hx.2
  have h1 :
      (x : ℂ) ^ (s - 1) =
        (a : ℂ) ^ (s - 1) * ((x / a : ℝ) : ℂ) ^ (s - 1) := by
    rw [← mul_cpow_ofReal_nonneg ha.le hxa.le]
    push_cast
    field_simp [ha0]
  have h2 :
      (((a : ℂ) - x) ^ (t - 1)) =
        (a : ℂ) ^ (t - 1) * ((1 - x / a : ℝ) : ℂ) ^ (t - 1) := by
    rw [← mul_cpow_ofReal_nonneg ha.le (sub_nonneg.mpr hxa1.le)]
    congr 1
    push_cast
    field_simp [ha0]
  simp only [f]
  rw [h1, h2]
  push_cast
  ring

/-- Exact affine simplex-slice identity. For a fixed outer coordinate `x < 1`, the
remaining inner edge has length `1-x`, so its singular integral is precisely the
scaled Beta factor used in the raised-box Dirichlet reduction. -/
theorem inner_simplex_slice_beta_identity
    {δ x : ℝ} (hx : x < 1) :
    (∫ y in (0)..(1 - x),
      (y : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
        (((1 - x : ℝ) : ℂ) - y) ^ (((2 : ℂ) - 1))) =
      ((1 - x : ℝ) : ℂ) ^ ((((1 - δ : ℝ) : ℂ) + 2 - 1)) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2 := by
  exact inner_scaled_beta_identity (sub_pos.mpr hx)

/-- Integrability of every nondegenerate affine simplex slice. -/
theorem inner_simplex_slice_convergent
    {δ x : ℝ} (hδ : δ < 1) (hx : x < 1) :
    IntervalIntegrable
      (fun y : ℝ =>
        (y : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (((1 - x : ℝ) : ℂ) - y) ^ (((2 : ℂ) - 1)))
      MeasureTheory.volume 0 (1 - x) := by
  exact scaled_beta_convergent
    (one_sub_delta_re_pos hδ) (by norm_num) (sub_pos.mpr hx)

/-- After the exact inner simplex slice is inserted, the remaining outer integral
is exactly the product `B(1-δ,3-δ) B(1-δ,2)`.  This is the second Beta factor in
the raised-box Dirichlet majorant.  The separate Fubini/endpoint theorem that
identifies the original nested simplex integral with this reduced outer integral
is intentionally not asserted here. -/
theorem outer_reduced_beta_product_identity (δ : ℝ) :
    (∫ x in (0)..1,
      ((x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
        (1 - (x : ℂ)) ^ ((((3 - δ : ℝ) : ℂ) - 1))) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2) =
      betaIntegral (((1 - δ : ℝ) : ℂ)) (((3 - δ : ℝ) : ℂ)) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2 := by
  rw [intervalIntegral.integral_mul_const]
  rfl

/-- Convergence of the inner Beta integral for `δ < 1`. -/
theorem inner_beta_convergent {δ : ℝ} (hδ : δ < 1) :
    IntervalIntegrable
      (fun x : ℝ =>
        (x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (1 - (x : ℂ)) ^ (((2 : ℂ) - 1)))
      MeasureTheory.volume 0 1 := by
  exact betaIntegral_convergent (one_sub_delta_re_pos hδ) (by norm_num)

/-- Convergence of the outer Beta integral `B(1-δ,3-δ)`. -/
theorem outer_beta_convergent {δ : ℝ} (hδ : δ < 1) :
    IntervalIntegrable
      (fun x : ℝ =>
        (x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (1 - (x : ℂ)) ^ ((((3 - δ : ℝ) : ℂ) - 1)))
      MeasureTheory.volume 0 1 := by
  exact betaIntegral_convergent
    (one_sub_delta_re_pos hδ) (three_sub_delta_re_pos hδ)

end GppRaisedBoxSimplexBetaLayer

#print axioms GppRaisedBoxSimplexBetaLayer.one_sub_delta_re_pos
#print axioms GppRaisedBoxSimplexBetaLayer.three_sub_delta_re_pos
#print axioms GppRaisedBoxSimplexBetaLayer.inner_scaled_beta_identity
#print axioms GppRaisedBoxSimplexBetaLayer.scaled_beta_convergent
#print axioms GppRaisedBoxSimplexBetaLayer.inner_simplex_slice_beta_identity
#print axioms GppRaisedBoxSimplexBetaLayer.inner_simplex_slice_convergent
#print axioms GppRaisedBoxSimplexBetaLayer.outer_reduced_beta_product_identity
#print axioms GppRaisedBoxSimplexBetaLayer.inner_beta_convergent
#print axioms GppRaisedBoxSimplexBetaLayer.outer_beta_convergent
