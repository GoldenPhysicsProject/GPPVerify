import GppVerify.CelestialHolography.RaisedBoxSimplexNestedReduction
import Mathlib.Tactic

/-!
# Raised-box simplex: Gamma closure

After the nested affine-simplex reduction, the majorant constant is

  B(1-delta, 3-delta) B(1-delta, 2).

For `delta < 1` the Beta parameters lie in the convergent half-plane.  The two
Beta--Gamma identities telescope at the shared `Gamma(3-delta)` factor and give

  Gamma(1-delta)^2 / Gamma(4-2 delta).

This file closes only that exact special-function algebra.  The regulator DCT
remains a separate theorem.
-/

namespace GppRaisedBoxSimplexGammaClosure

open Complex
open GppRaisedBoxSimplexBetaLayer
open GppRaisedBoxSimplexNestedReduction

/-- Exact Beta-product to Gamma-ratio identity for the raised-box simplex
majorant. -/
theorem beta_product_eq_gamma_ratio
    {δ : ℝ} (hδ : δ < 1) :
    betaIntegral (((1 - δ : ℝ) : ℂ)) (((3 - δ : ℝ) : ℂ)) *
        betaIntegral (((1 - δ : ℝ) : ℂ)) 2 =
      Gamma (((1 - δ : ℝ) : ℂ)) ^ 2 /
        Gamma (((4 - 2 * δ : ℝ) : ℂ)) := by
  let a : ℂ := ((1 - δ : ℝ) : ℂ)
  let b : ℂ := ((3 - δ : ℝ) : ℂ)
  let c : ℂ := ((4 - 2 * δ : ℝ) : ℂ)
  have ha : 0 < a.re := by
    dsimp [a]
    simpa using sub_pos.mpr hδ
  have hb : 0 < b.re := by
    dsimp [b]
    simp
    linarith
  have hc : 0 < c.re := by
    dsimp [c]
    simp
    linarith
  have hb_eq : a + 2 = b := by
    dsimp [a, b]
    push_cast
    ring
  have hc_eq : a + b = c := by
    dsimp [a, b, c]
    push_cast
    ring
  have h1 := Gamma_mul_Gamma_eq_betaIntegral ha (show 0 < (2 : ℂ).re by norm_num)
  have h2 := Gamma_mul_Gamma_eq_betaIntegral ha hb
  have h1' : Gamma a = Gamma b * betaIntegral a 2 := by
    rw [hb_eq] at h1
    simpa using h1
  have h2' : Gamma a * Gamma b = Gamma c * betaIntegral a b := by
    rw [hc_eq] at h2
    exact h2
  have hGc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have hGb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  change betaIntegral a b * betaIntegral a 2 = Gamma a ^ 2 / Gamma c
  field_simp [hGc]
  calc
    (betaIntegral a b * betaIntegral a 2) * Gamma c
        = Gamma c * (betaIntegral a b * betaIntegral a 2) := by ring
    _ = (Gamma c * betaIntegral a b) * betaIntegral a 2 := by ring
    _ = (Gamma a * Gamma b) * betaIntegral a 2 := by rw [← h2']
    _ = Gamma a * (Gamma b * betaIntegral a 2) := by ring
    _ = Gamma a * Gamma a := by rw [← h1']
    _ = Gamma a ^ 2 := by ring

/-- Therefore the full nested simplex majorant has the closed Gamma ratio. -/
theorem nestedSimplexIntegral_eq_gamma_ratio
    {δ : ℝ} (hδ : δ < 1) :
    nestedSimplexIntegral δ =
      Gamma (((1 - δ : ℝ) : ℂ)) ^ 2 /
        Gamma (((4 - 2 * δ : ℝ) : ℂ)) := by
  rw [nestedSimplexIntegral_eq_beta_product hδ]
  exact beta_product_eq_gamma_ratio hδ

end GppRaisedBoxSimplexGammaClosure

#print axioms GppRaisedBoxSimplexGammaClosure.beta_product_eq_gamma_ratio
#print axioms GppRaisedBoxSimplexGammaClosure.nestedSimplexIntegral_eq_gamma_ratio
