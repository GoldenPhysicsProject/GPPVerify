import GppVerify.CelestialHolography.RaisedBoxSimplexMeasureBridge
import Mathlib.Tactic

/-!
# Raised-box simplex: nested integral reduction

This file closes the bookkeeping step between the actual nested affine-simplex
integral used by the one-channel majorant and the already-proved reduced outer
Beta integral. Endpoint `x=1` is handled explicitly; no Fubini interchange is
used here because the simplex has already been parameterized as an iterated
integral.

The remaining regulator theorem after this layer is dominated convergence for
the original raised-box integrand.
-/

namespace GppRaisedBoxSimplexNestedReduction

open Complex
open scoped Interval
open GppRaisedBoxSimplexBetaLayer

/-- The two-dimensional affine-simplex singular integral after the spectator
simplex coordinate has been integrated out. -/
noncomputable def nestedSimplexIntegral (δ : ℝ) : ℂ :=
  ∫ x in (0)..1,
    (x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
      (∫ y in (0)..(1 - x),
        (y : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (((1 - x : ℝ) : ℂ) - y) ^ (((2 : ℂ) - 1)))

/-- Exact nested-to-reduced simplex identity. The only exceptional outer
endpoint is `x=1`; both sides vanish there when `δ<1`. -/
theorem nestedSimplexIntegral_eq_reduced
    {δ : ℝ} (hδ : δ < 1) :
    nestedSimplexIntegral δ =
      ∫ x in (0)..1,
        ((x : ℂ) ^ ((((1 - δ : ℝ) : ℂ) - 1)) *
          (1 - (x : ℂ)) ^ ((((3 - δ : ℝ) : ℂ) - 1))) *
          betaIntegral (((1 - δ : ℝ) : ℂ)) 2 := by
  unfold nestedSimplexIntegral
  apply intervalIntegral.integral_congr_ae
  refine Filter.Eventually.of_forall ?_
  intro x hx
  rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
  by_cases hx1 : x = 1
  · subst x
    have hne : ((3 : ℂ) - (δ : ℂ) - 1) ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp at hre
      linarith
    simp [hne]
  · have hxlt : x < 1 := lt_of_le_of_ne hx.2 hx1
    rw [inner_simplex_slice_beta_identity hxlt]
    have hbase : ((1 - (x : ℝ) : ℝ) : ℂ) = 1 - (x : ℂ) := by
      push_cast
      ring
    have hexp :
        ((((1 - δ : ℝ) : ℂ) + 2 - 1)) =
          ((((3 - δ : ℝ) : ℂ) - 1)) := by
      push_cast
      ring
    rw [hbase, hexp]
    ring

/-- The full nested majorant integral is exactly the product of the two Beta
factors. -/
theorem nestedSimplexIntegral_eq_beta_product
    {δ : ℝ} (hδ : δ < 1) :
    nestedSimplexIntegral δ =
      betaIntegral (((1 - δ : ℝ) : ℂ)) (((3 - δ : ℝ) : ℂ)) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2 := by
  rw [nestedSimplexIntegral_eq_reduced hδ]
  exact outer_reduced_beta_product_identity δ

end GppRaisedBoxSimplexNestedReduction

#print axioms GppRaisedBoxSimplexNestedReduction.nestedSimplexIntegral_eq_reduced
#print axioms GppRaisedBoxSimplexNestedReduction.nestedSimplexIntegral_eq_beta_product
