import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Twisted convolution squares: the cos and cosh polarization identities

Source: Grok ("Heart of the Cosmos"), `GPPDiscovery5/derivation/ARP.md` §G.6 items 1 and 2
(`twist_cos_sum`, `twist_cosh_krein`). Daniel Toupin / Golden Physics Project, with AI assistance
from Grok (statements) and Claude Code (formalization).

Convention (ARP.md §A): `f̃(u) = f(−u)` and `(f ∗ g̃)(r) = ∫ f(u) g(u − r) du`, so
`(f ∗ f̃)(r) = ∫ f(u) f(u − r) du`. Write `conv f g r` for `∫ f(u) g(u − r) du`.

* `twist_cos_sum`: `conv (f cos θ·) (f cos θ·) r + conv (f sin θ·) (f sin θ·) r
  = cos(θ r) · conv f f r`.
* `twist_cosh_krein`: with `h± = e^{±θu} f`,
  `conv h₊ h₋ r + conv h₋ h₊ r = 2 cosh(θ r) · conv f f r`.
* `parallelogram_cplx`: `|A + iB|² + |A − iB|² = 2|A|² + 2|B|²` (the zero-side identity).

**Correction to the source statement.** ARP.md §G.6 item 1 writes the cos identity with a factor
`2` on the left, `2cos(θr)(f∗f̃)(r) = …`. Under the stated convention the right-hand side equals
`cos(θr)(f∗f̃)(r)`, because `cos a cos b + sin a sin b = cos(a − b)` with `a − b = θr`. The factor
`2` is correct for the cosh identity (item 2), where the two terms contribute `e^{θr}` and
`e^{−θr}`. This file proves the identities as they hold; the discrepancy is recorded for Grok.

**Scope.** Real-valued `f` on `ℝ` with Lebesgue measure. The cos identity assumes `f` is a.e.
strongly measurable and `u ↦ f(u) f(u − r)` is integrable at the given `r`; the cosh identity needs
no integrability. No claim about RH.
-/

set_option autoImplicit false

open MeasureTheory

namespace GppTwistConvolution

/-- `conv f g r = ∫ f(u) g(u − r) du`, i.e. `(f ∗ g̃)(r)`. -/
noncomputable def conv (f g : ℝ → ℝ) (r : ℝ) : ℝ := ∫ u, f u * g (u - r)

/-- **cos polarization.** The cos and sin twists sum to `cos(θ r)` times the untwisted square. -/
theorem twist_cos_sum {f : ℝ → ℝ} (hm : AEStronglyMeasurable f volume) (θ r : ℝ)
    (hint : Integrable (fun u => f u * f (u - r)) volume) :
    conv (fun u => f u * Real.cos (θ * u)) (fun u => f u * Real.cos (θ * u)) r +
      conv (fun u => f u * Real.sin (θ * u)) (fun u => f u * Real.sin (θ * u)) r =
      Real.cos (θ * r) * conv f f r := by
  have hshift : AEStronglyMeasurable (fun u => f (u - r)) volume :=
    hm.comp_quasiMeasurePreserving (measurePreserving_sub_right volume r).quasiMeasurePreserving
  have hmeas : ∀ (c : ℝ → ℝ), Continuous c → AEStronglyMeasurable
      (fun u => f u * c u * (f (u - r) * c (u - r))) volume := fun c hc =>
    (hm.mul hc.aestronglyMeasurable).mul (hshift.mul (hc.comp (continuous_sub_right r)).aestronglyMeasurable)
  have hI : ∀ (c : ℝ → ℝ), Continuous c → (∀ x, |c x| ≤ 1) →
      Integrable (fun u => f u * c u * (f (u - r) * c (u - r))) volume := by
    intro c hc hb
    refine hint.norm.mono' (hmeas c hc) (Filter.Eventually.of_forall fun u => ?_)
    have h1 := hb u
    have h2 := hb (u - r)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |f u * c u * (f (u - r) * c (u - r))|
        = |f u * f (u - r)| * (|c u| * |c (u - r)|) := by
          rw [← abs_mul (c u) (c (u - r)), ← abs_mul]; congr 1; ring
      _ ≤ |f u * f (u - r)| * (1 * 1) := by
          gcongr
      _ = |f u * f (u - r)| := by ring
  have hc := hI (fun x => Real.cos (θ * x))
    (by fun_prop) (fun x => Real.abs_cos_le_one _)
  have hs := hI (fun x => Real.sin (θ * x))
    (by fun_prop) (fun x => Real.abs_sin_le_one _)
  unfold conv
  rw [← integral_add hc hs, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hcos : Real.cos (θ * r) = Real.cos (θ * u - θ * (u - r)) := by
    congr 1; ring
  simp only []
  rw [hcos, Real.cos_sub]
  ring

/-- **cosh polarization (Krein form).** -/
theorem twist_cosh_krein (f : ℝ → ℝ) (θ r : ℝ) :
    conv (fun u => Real.exp (θ * u) * f u) (fun u => Real.exp (-θ * u) * f u) r +
      conv (fun u => Real.exp (-θ * u) * f u) (fun u => Real.exp (θ * u) * f u) r =
      2 * Real.cosh (θ * r) * conv f f r := by
  unfold conv
  have h1 : (fun u => Real.exp (θ * u) * f u * (Real.exp (-θ * (u - r)) * f (u - r))) =
      fun u => Real.exp (θ * r) * (f u * f (u - r)) := by
    funext u
    have : Real.exp (θ * u) * Real.exp (-θ * (u - r)) = Real.exp (θ * r) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ = (Real.exp (θ * u) * Real.exp (-θ * (u - r))) * (f u * f (u - r)) := by ring
      _ = _ := by rw [this]
  have h2 : (fun u => Real.exp (-θ * u) * f u * (Real.exp (θ * (u - r)) * f (u - r))) =
      fun u => Real.exp (-(θ * r)) * (f u * f (u - r)) := by
    funext u
    have : Real.exp (-θ * u) * Real.exp (θ * (u - r)) = Real.exp (-(θ * r)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ = (Real.exp (-θ * u) * Real.exp (θ * (u - r))) * (f u * f (u - r)) := by ring
      _ = _ := by rw [this]
  rw [h1, h2, integral_const_mul, integral_const_mul, Real.cosh_eq]
  ring

/-- Zero-side parallelogram identity. -/
theorem parallelogram_cplx (A B : ℂ) :
    ‖A + Complex.I * B‖ ^ 2 + ‖A - Complex.I * B‖ ^ 2 = 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

end GppTwistConvolution
