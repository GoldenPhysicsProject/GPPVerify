import GppVerify.RiemannHypothesis.PasterskiShaoDictionary
import GppVerify.CelestialHolography.ConformalShadowPrincipalSeries
import GppVerify.CelestialHolography.PSSShadowTransform
import GppVerify.CelestialHolography.PSSNormalizability
import GppVerify.StandardModel.ThreeGenerations

/-!
# The ladder of shadow data, indexed by dimension

One structure collects, for each boundary dimension `d`, the shadow datum already proved in the
tree, and the doubling `(d, Δ) ↦ (2d, 2Δ)` joins consecutive rungs `d = 2^n`.

* `ShadowRung d` (S-A1): the label involution `shadowDim d`, its fixed locus
  `Re Δ = d/2` (exactly the locus where the shadow is complex conjugation), delta-normalisability
  `RadialDeltaNormalisable d Δ ↔ Re Δ = d/2`, and the two covariances of the integral shadow
  operator `shadow d Δ` (translation, and dilation with output weight `d - Δ`).
  `shadowRung d : ShadowRung d` holds for every `d : ℕ`.
* `conformalShadow_double`, `double_fixed_iff`, `shadowDim_double`, `normalisable_double` (S-A2):
  the doubling carries the shadow involution to the shadow involution, the fixed locus onto the
  fixed locus (both directions) and principal-series normalisability onto principal-series
  normalisability, for every `d`. `doubled_arithmetic_shadow_of_double` recovers the in-tree
  `d = 1 → 2` theorem `doubled_arithmetic_shadow_eq_two_dimensional` as the instance `d = 1`.
* `rungDim n = 2^n` (the Cayley-Dickson dimension), `rungDim_succ`, `ladder_rung`, `ladder_joint`
  (S-A3): rung `n` is `ShadowRung (2^n)` and the joint between rung `n` and rung `n + 1` is the
  S-A2 doubling at `d = 2^n`.
-/

open Complex
open scoped ComplexConjugate

namespace GppShadowLadder

open GppPSSShadowTransform GppConformalShadowPrincipalSeries GppPSSNormalizability

/-- **S-A1.** The shadow datum at boundary dimension `d`. -/
structure ShadowRung (d : ℕ) : Prop where
  involutive : ∀ Δ : ℂ, shadowDim d (shadowDim d Δ) = Δ
  fixed_locus : ∀ Δ : ℂ, shadowDim d Δ = conj Δ ↔ Δ.re = (d : ℝ) / 2
  normalisable : ∀ Δ : ℂ, RadialDeltaNormalisable d Δ ↔ Δ.re = (d : ℝ) / 2
  translate : ∀ (Δ : ℂ) (f : (Fin d → ℝ) → ℂ) (a w : Fin d → ℝ),
    shadow d Δ (fun z => f (z + a)) w = shadow d Δ f (w + a)
  dilate : ∀ (Δ : ℂ) {lam : ℝ}, 0 < lam → ∀ (f : (Fin d → ℝ) → ℂ) (w : Fin d → ℝ),
    shadow d Δ (GppPSSShadowTransform.dilate Δ lam f) w =
      GppPSSShadowTransform.dilate (shadowDim d Δ) lam (shadow d Δ f) w

/-- Every boundary dimension carries a shadow rung. -/
theorem shadowRung (d : ℕ) : ShadowRung d where
  involutive := shadowDim_involutive d
  fixed_locus := fun Δ => by
    rw [GppPasterskiShaoDictionary.shadowDim_eq_conformalShadow]
    exact conformalShadow_eq_conj_iff (d : ℝ) Δ
  normalisable := radialDeltaNormalisable_iff d
  translate := shadow_translate d
  dilate := fun Δ _ hlam f w => shadow_dilate d Δ hlam f w

/-! ### S-A2: the doubling joint -/

/-- The doubling `(d, Δ) ↦ (2d, 2Δ)` carries the shadow to twice the shadow. -/
theorem conformalShadow_double (d : ℝ) (Δ : ℂ) :
    conformalShadow (2 * d) (2 * Δ) = 2 * conformalShadow d Δ := by
  unfold conformalShadow
  push_cast
  ring

/-- The doubling carries the fixed locus onto the fixed locus, in both directions. -/
theorem double_fixed_iff (d : ℝ) (Δ : ℂ) :
    (2 * Δ).re = (2 * d) / 2 ↔ Δ.re = d / 2 := by
  have : (2 * Δ).re = 2 * Δ.re := by simp
  rw [this]
  constructor <;> intro h <;> linarith

/-- Label form of the doubling for natural-number dimensions. -/
theorem shadowDim_double (d : ℕ) (Δ : ℂ) :
    shadowDim (2 * d) (2 * Δ) = 2 * shadowDim d Δ := by
  unfold shadowDim
  push_cast
  ring

/-- The doubling carries principal-series normalisability onto principal-series
normalisability. -/
theorem normalisable_double (d : ℕ) (Δ : ℂ) :
    RadialDeltaNormalisable (2 * d) (2 * Δ) ↔ RadialDeltaNormalisable d Δ := by
  rw [radialDeltaNormalisable_iff, radialDeltaNormalisable_iff]
  have := double_fixed_iff (d : ℝ) Δ
  push_cast
  exact this

/-- The in-tree `d = 1 → 2` doubling theorem, as the instance `d = 1` of
`conformalShadow_double` (`celestialDelta s = 2 s`). -/
theorem doubled_arithmetic_shadow_of_double (s : ℂ) :
    GppScaleShadow.celestialDelta (1 - s) =
      conformalShadow 2 (GppScaleShadow.celestialDelta s) := by
  have h := conformalShadow_double 1 s
  unfold GppScaleShadow.celestialDelta
  rw [show (2 : ℝ) = 2 * 1 by norm_num, h]
  unfold conformalShadow
  push_cast
  ring

/-! ### S-A3: the ladder along the Cayley-Dickson dimensions -/

/-- The dimension of rung `n`: the Cayley-Dickson dimension `2^n`. -/
def rungDim (n : ℕ) : ℕ := GppSM.cdDim n

theorem rungDim_zero : rungDim 0 = 1 := by
  unfold rungDim GppSM.cdDim; norm_num

theorem rungDim_succ (n : ℕ) : rungDim (n + 1) = 2 * rungDim n := by
  unfold rungDim GppSM.cdDim; ring

/-- Rung `n` is the shadow datum in dimension `2^n`. -/
theorem ladder_rung (n : ℕ) : ShadowRung (rungDim n) := shadowRung _

/-- The joint between rung `n` and rung `n + 1` is the doubling: label map, fixed locus and
principal-series normalisability all correspond. -/
theorem ladder_joint (n : ℕ) (Δ : ℂ) :
    shadowDim (rungDim (n + 1)) (2 * Δ) = 2 * shadowDim (rungDim n) Δ ∧
    ((2 * Δ).re = (rungDim (n + 1) : ℝ) / 2 ↔ Δ.re = (rungDim n : ℝ) / 2) ∧
    (RadialDeltaNormalisable (rungDim (n + 1)) (2 * Δ) ↔ RadialDeltaNormalisable (rungDim n) Δ) := by
  rw [rungDim_succ]
  refine ⟨shadowDim_double _ Δ, ?_, normalisable_double _ Δ⟩
  have := double_fixed_iff (rungDim n : ℝ) Δ
  push_cast
  exact this

/-- Rung 0 is the arithmetic line: the shadow is `s ↦ 1 - s`. -/
theorem rung_zero_shadow (Δ : ℂ) : shadowDim (rungDim 0) Δ = 1 - Δ := by
  rw [rungDim_zero]
  unfold shadowDim
  simp

#print axioms shadowRung
#print axioms conformalShadow_double
#print axioms double_fixed_iff
#print axioms shadowDim_double
#print axioms normalisable_double
#print axioms doubled_arithmetic_shadow_of_double
#print axioms rungDim_succ
#print axioms ladder_rung
#print axioms ladder_joint
#print axioms rung_zero_shadow

end GppShadowLadder
