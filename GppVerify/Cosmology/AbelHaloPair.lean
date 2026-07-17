import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The pseudo-isothermal halo pair: forward Abel projection and its inversion, exactly

Thread H of `docs/FORMALIZATION_PLAN.md`, from ONON5213.tex Chapter "Dark Matter:
Geometric Origin from Shadow Symmetry" (`thm:surface-density-haar`, `thm:abel-inversion`,
and the boxed pseudo-isothermal profile). The chapter's checkable analytic core is a
matched pair of improper integrals:

* **Forward projection** (`abel_forward`): the line-of-sight projection of the
  pseudo-isothermal density `ρ(r) = ρ₀·r_c²/(r²+r_c²)`,
  `Σ(b) = 2∫_b^∞ ρ(r)·r/√(r²−b²) dr`, evaluates **exactly** to the chapter's holographic
  surface density `π·ρ₀·r_c²/√(b²+r_c²)`. Antiderivative:
  `G(r) = (2r_c²/A)·arctan(√(r²−b²)/A)` with `A = √(b²+r_c²)` — the same
  `integral_Ioi_of_hasDerivAt_of_nonneg` machinery as Threads C2/A2/K, with the
  Cauchy-kernel `1/(A²+u²)` soul of `CauchyKernelPositive.lean`.
* **Abel inversion, instantiated** (`abel_inverse_eval`, `dm_profile_boxed`): the
  chapter's inversion formula `ρ(r) = −(1/π)∫_r^∞ Σ'(b)/√(b²−r²) db` applied to that
  surface density — whose derivative produces the integrand
  `π ρ₀ r_c²·b/(√(b²−r²)·√(b²+r_c²)³)` — returns **exactly** the boxed profile
  `ρ_DM(r) = ρ₀/(1+(r/r_c)²)`. Antiderivative:
  `H(b) = (√(b²−r²)/√(b²+r_c²))/(r²+r_c²)`.

Together the roundtrip is exact and kernel-checked: the dark-matter core profile the
chapter compares against galaxy rotation curves is a theorem pair, not a calculation.

**What is deliberately NOT claimed**: the general Abel inversion theorem
(`thm:abel-formula`, uniqueness for arbitrary profiles via Hankel duality) is not
formalized — this file proves both directions **for the chapter's profile**, which is
all its physics uses. The Haar-measure derivation of the kernel normalization and the
identification `ρ₀ = α·ρ_b` (Conjecture `thm:dm-abundance`) are the chapter's physics
inputs, not claimed.
-/

namespace GppHalo

open MeasureTheory Set Filter

/-- Cosmetic bridge: the pseudo-isothermal profile in its two standard forms. -/
theorem pseudo_isothermal_eq {rc : ℝ} (hrc : 0 < rc) (r : ℝ) :
    rc^2 / (r^2 + rc^2) = 1 / (1 + (r/rc)^2) := by
  have h1 : (rc:ℝ)^2 ≠ 0 := by positivity
  have h2 : (r:ℝ)^2 + rc^2 ≠ 0 := by positivity
  have h3 : (1:ℝ) + (r/rc)^2 ≠ 0 := by positivity
  rw [div_eq_div_iff h2 h3, div_pow, one_mul]
  field_simp
  ring

/-- The inner derivative `(t² − c)' = 2t`, shared by both halves. -/
theorem hasDerivAt_sq_sub (c t : ℝ) :
    HasDerivAt (fun x : ℝ => x^2 - c) (2*t) t := by
  simpa using (hasDerivAt_pow 2 t).sub_const c

/-- The inner derivative `(t² + c)' = 2t`. -/
theorem hasDerivAt_sq_add (c t : ℝ) :
    HasDerivAt (fun x : ℝ => x^2 + c) (2*t) t := by
  simpa using (hasDerivAt_pow 2 t).add_const c

/-! ## H1: the forward Abel projection of the pseudo-isothermal profile -/

/-- **The forward Abel projection, exactly**: for `r_c > 0` and impact parameter
    `b ≥ 0`, `∫_b^∞ 2·(r_c²/(r²+r_c²))·(r/√(r²−b²)) dr = π·r_c²/√(b²+r_c²)` — the
    chapter's holographic surface density from its boxed density profile. -/
theorem abel_forward {rc b : ℝ} (hrc : 0 < rc) (hb : 0 ≤ b) :
    ∫ r in Ioi b, 2 * (rc^2 / (r^2 + rc^2)) * (r / Real.sqrt (r^2 - b^2)) =
      Real.pi * rc^2 / Real.sqrt (b^2 + rc^2) := by
  set A : ℝ := Real.sqrt (b^2 + rc^2) with hA
  have hApos : 0 < A := Real.sqrt_pos.mpr (by positivity)
  have hA2 : A^2 = b^2 + rc^2 := Real.sq_sqrt (by positivity)
  have hrcden : ∀ r : ℝ, r^2 + rc^2 ≠ 0 := fun r => by positivity
  -- the antiderivative G(r) = (2 r_c²/A) · arctan(√(r²−b²)/A)
  have hderiv : ∀ r ∈ Ioi b,
      HasDerivAt (fun t : ℝ => 2 * rc^2 / A * Real.arctan (Real.sqrt (t^2 - b^2) / A))
        (2 * (rc^2 / (r^2 + rc^2)) * (r / Real.sqrt (r^2 - b^2))) r := by
    intro r hr
    have hbr : b < r := hr
    have hrb : (0:ℝ) < r^2 - b^2 := by nlinarith
    have hsqrtpos : (0:ℝ) < Real.sqrt (r^2 - b^2) := Real.sqrt_pos.mpr hrb
    have hsqrtsq : (Real.sqrt (r^2 - b^2))^2 = r^2 - b^2 := Real.sq_sqrt hrb.le
    have hsq : HasDerivAt (fun t : ℝ => Real.sqrt (t^2 - b^2))
        ((2*r) / (2 * Real.sqrt (r^2 - b^2))) r :=
      (hasDerivAt_sq_sub (b^2) r).sqrt hrb.ne'
    have hdiv : HasDerivAt (fun t : ℝ => Real.sqrt (t^2 - b^2) / A)
        ((2*r) / (2 * Real.sqrt (r^2 - b^2)) / A) r := hsq.div_const A
    have harct : HasDerivAt
        (fun t : ℝ => Real.arctan (Real.sqrt (t^2 - b^2) / A))
        (1 / (1 + (Real.sqrt (r^2 - b^2) / A)^2) *
          ((2*r) / (2 * Real.sqrt (r^2 - b^2)) / A)) r :=
      hdiv.arctan
    have h := harct.const_mul (2 * rc^2 / A)
    have hstep : 1 + (Real.sqrt (r^2 - b^2) / A)^2 = (r^2 + rc^2) / A^2 := by
      rw [div_pow, hsqrtsq, hA2]
      have hden : b^2 + rc^2 ≠ 0 := by positivity
      field_simp
      ring
    have hval : 2 * rc^2 / A * (1 / (1 + (Real.sqrt (r^2 - b^2) / A)^2) *
        ((2*r) / (2 * Real.sqrt (r^2 - b^2)) / A)) =
        2 * (rc^2 / (r^2 + rc^2)) * (r / Real.sqrt (r^2 - b^2)) := by
      rw [hstep, one_div_div]
      field_simp [hApos.ne', hsqrtpos.ne', hrcden r]
      ring
    rw [hval] at h
    exact h
  -- endpoint continuity: the antiderivative is globally continuous
  have hcont : ContinuousWithinAt
      (fun t : ℝ => 2 * rc^2 / A * Real.arctan (Real.sqrt (t^2 - b^2) / A)) (Ici b) b := by
    apply Continuous.continuousWithinAt
    exact continuous_const.mul (Real.continuous_arctan.comp
      ((Real.continuous_sqrt.comp ((continuous_pow 2).sub continuous_const)).div_const A))
  -- nonnegative integrand
  have hpos : ∀ r ∈ Ioi b,
      0 ≤ 2 * (rc^2 / (r^2 + rc^2)) * (r / Real.sqrt (r^2 - b^2)) := by
    intro r hr
    have hbr : b < r := hr
    have hr0 : (0:ℝ) < r := lt_of_le_of_lt hb hbr
    have hrb : (0:ℝ) < r^2 - b^2 := by nlinarith
    have hsqrtpos : (0:ℝ) < Real.sqrt (r^2 - b^2) := Real.sqrt_pos.mpr hrb
    positivity
  -- the limit at infinity: arctan(√(t²−b²)/A) → π/2
  have hinner : Tendsto (fun t : ℝ => Real.sqrt (t^2 - b^2) / A) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ ((tendsto_atTop_add_const_right atTop (-b)
      tendsto_id).atTop_div_const hApos)
    filter_upwards [eventually_ge_atTop b] with t ht
    have h1 : (0:ℝ) ≤ t - b := by linarith
    have h2 : (t - b)^2 ≤ t^2 - b^2 := by nlinarith
    have h3 : t - b ≤ Real.sqrt (t^2 - b^2) := by
      calc t - b = Real.sqrt ((t - b)^2) := (Real.sqrt_sq h1).symm
        _ ≤ Real.sqrt (t^2 - b^2) := Real.sqrt_le_sqrt h2
    have h4 : t + -b ≤ Real.sqrt (t^2 - b^2) := by linarith
    have h5 := mul_le_mul_of_nonneg_right h4 (le_of_lt (inv_pos.mpr hApos))
    simpa [div_eq_mul_inv] using h5
  have htop : Tendsto
      (fun t : ℝ => 2 * rc^2 / A * Real.arctan (Real.sqrt (t^2 - b^2) / A))
      atTop (nhds (2 * rc^2 / A * (Real.pi / 2))) := by
    have h : Tendsto (fun t : ℝ => Real.arctan (Real.sqrt (t^2 - b^2) / A))
        atTop (nhds (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hinner
    exact h.const_mul _
  have key := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos htop
  rw [key]
  have hGb : 2 * rc^2 / A * Real.arctan (Real.sqrt (b^2 - b^2) / A) = 0 := by
    rw [sub_self, Real.sqrt_zero, zero_div, Real.arctan_zero, mul_zero]
  rw [hGb, sub_zero, div_mul_eq_mul_div,
    show 2 * rc^2 * (Real.pi / 2) = Real.pi * rc^2 by ring]

/-! ## H2: the Abel inversion, instantiated at the holographic surface density -/

/-- **The Abel inversion integral, exactly**: for `r_c > 0` and radius `r ≥ 0`,
    `∫_r^∞ b/(√(b²−r²)·√(b²+r_c²)³) db = 1/(r²+r_c²)` — the integral produced by the
    chapter's inversion formula applied to `Σ(b) = π ρ₀ r_c²/√(b²+r_c²)`. -/
theorem abel_inverse_eval {rc r : ℝ} (hrc : 0 < rc) (hr : 0 ≤ r) :
    ∫ b in Ioi r, b / (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)^3) =
      1 / (r^2 + rc^2) := by
  have hrden : (0:ℝ) < r^2 + rc^2 := by positivity
  -- the antiderivative H(b) = (√(b²−r²)/√(b²+r_c²)) / (r²+r_c²)
  have hderiv : ∀ b ∈ Ioi r,
      HasDerivAt (fun t : ℝ => Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2) /
        (r^2 + rc^2))
        (b / (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)^3)) b := by
    intro b hbmem
    have hrb : r < b := hbmem
    have hbr : (0:ℝ) < b^2 - r^2 := by nlinarith
    have hbc : (0:ℝ) < b^2 + rc^2 := by positivity
    have hsm : (0:ℝ) < Real.sqrt (b^2 - r^2) := Real.sqrt_pos.mpr hbr
    have hsp : (0:ℝ) < Real.sqrt (b^2 + rc^2) := Real.sqrt_pos.mpr hbc
    have hsmsq : (Real.sqrt (b^2 - r^2))^2 = b^2 - r^2 := Real.sq_sqrt hbr.le
    have hspsq : (Real.sqrt (b^2 + rc^2))^2 = b^2 + rc^2 := Real.sq_sqrt hbc.le
    have h1 : HasDerivAt (fun t : ℝ => Real.sqrt (t^2 - r^2))
        ((2*b) / (2 * Real.sqrt (b^2 - r^2))) b :=
      (hasDerivAt_sq_sub (r^2) b).sqrt hbr.ne'
    have h2 : HasDerivAt (fun t : ℝ => Real.sqrt (t^2 + rc^2))
        ((2*b) / (2 * Real.sqrt (b^2 + rc^2))) b :=
      (hasDerivAt_sq_add (rc^2) b).sqrt hbc.ne'
    have hq : HasDerivAt
        (fun t : ℝ => Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2) / (r^2 + rc^2))
        (((2*b) / (2 * Real.sqrt (b^2 - r^2)) * Real.sqrt (b^2 + rc^2) -
          Real.sqrt (b^2 - r^2) * ((2*b) / (2 * Real.sqrt (b^2 + rc^2)))) /
            (Real.sqrt (b^2 + rc^2))^2 / (r^2 + rc^2)) b :=
      (h1.div h2 hsp.ne').div_const (r^2 + rc^2)
    -- massage the derivative value in two deterministic stages
    have e1 : (2*b) / (2 * Real.sqrt (b^2 - r^2)) * Real.sqrt (b^2 + rc^2) -
        Real.sqrt (b^2 - r^2) * ((2*b) / (2 * Real.sqrt (b^2 + rc^2))) =
        b * ((Real.sqrt (b^2 + rc^2))^2 - (Real.sqrt (b^2 - r^2))^2) /
          (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)) := by
      field_simp [hsm.ne', hsp.ne']
      ring
    have hu3 : Real.sqrt (b^2 + rc^2)^3 = (b^2 + rc^2) * Real.sqrt (b^2 + rc^2) := by
      rw [show Real.sqrt (b^2 + rc^2)^3
          = Real.sqrt (b^2 + rc^2)^2 * Real.sqrt (b^2 + rc^2) by ring, hspsq]
    have hval : ((2*b) / (2 * Real.sqrt (b^2 - r^2)) * Real.sqrt (b^2 + rc^2) -
        Real.sqrt (b^2 - r^2) * ((2*b) / (2 * Real.sqrt (b^2 + rc^2)))) /
          (Real.sqrt (b^2 + rc^2))^2 / (r^2 + rc^2) =
        b / (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)^3) := by
      rw [e1, hsmsq, hspsq,
        show b^2 + rc^2 - (b^2 - r^2) = r^2 + rc^2 by ring, hu3]
      field_simp [hsm.ne', hsp.ne', hrden.ne', hbc.ne']
      ring
    rw [hval] at hq
    exact hq
  -- endpoint continuity (the denominator sqrt never vanishes)
  have hcont : ContinuousWithinAt
      (fun t : ℝ => Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2) / (r^2 + rc^2))
      (Ici r) r := by
    apply Continuous.continuousWithinAt
    apply Continuous.div_const
    apply Continuous.div
    · exact Real.continuous_sqrt.comp ((continuous_pow 2).sub continuous_const)
    · exact Real.continuous_sqrt.comp ((continuous_pow 2).add continuous_const)
    · intro t
      exact (Real.sqrt_pos.mpr (by positivity)).ne'
  -- nonnegative integrand
  have hpos : ∀ b ∈ Ioi r,
      0 ≤ b / (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)^3) := by
    intro b hbmem
    have hrb : r < b := hbmem
    have hb0 : (0:ℝ) < b := lt_of_le_of_lt hr hrb
    have hbr : (0:ℝ) < b^2 - r^2 := by nlinarith
    have hsm : (0:ℝ) < Real.sqrt (b^2 - r^2) := Real.sqrt_pos.mpr hbr
    have hsp : (0:ℝ) < Real.sqrt (b^2 + rc^2) := Real.sqrt_pos.mpr (by positivity)
    positivity
  -- the limit at infinity, via the square of the ratio
  have hsq_lim : Tendsto
      (fun t : ℝ => (Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2))^2)
      atTop (nhds 1) := by
    have hcong : ∀ᶠ t in atTop,
        (Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2))^2 =
          1 - (r^2 + rc^2) / (t^2 + rc^2) := by
      filter_upwards [eventually_gt_atTop r] with t ht
      have h1 : (0:ℝ) < t^2 - r^2 := by nlinarith [lt_of_le_of_lt hr ht]
      have h2 : (0:ℝ) < t^2 + rc^2 := by positivity
      rw [div_pow, Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
      field_simp
    rw [tendsto_congr' hcong]
    have hdenom : Tendsto (fun t : ℝ => t^2 + rc^2) atTop atTop :=
      tendsto_atTop_add_const_right atTop (rc^2) (tendsto_pow_atTop two_ne_zero)
    have hdiv : Tendsto (fun t : ℝ => (r^2 + rc^2) / (t^2 + rc^2)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds hdenom
    have h := tendsto_const_nhds.sub hdiv
    simpa using h
  have hratio : Tendsto (fun t : ℝ => Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2))
      atTop (nhds 1) := by
    have h := (Real.continuous_sqrt.tendsto 1).comp hsq_lim
    rw [Real.sqrt_one] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro t
    exact Real.sqrt_sq (by positivity)
  have htop : Tendsto
      (fun t : ℝ => Real.sqrt (t^2 - r^2) / Real.sqrt (t^2 + rc^2) / (r^2 + rc^2))
      atTop (nhds (1 / (r^2 + rc^2))) := hratio.div_const _
  have key := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos htop
  rw [key]
  have hHr : Real.sqrt (r^2 - r^2) / Real.sqrt (r^2 + rc^2) / (r^2 + rc^2) = 0 := by
    rw [sub_self, Real.sqrt_zero, zero_div, zero_div]
  rw [hHr, sub_zero]

/-- **The boxed pseudo-isothermal profile** (`thm:abel-inversion`): the chapter's
    inversion output `ρ₀·r_c² × (inversion integral)` is exactly
    `ρ_DM(r) = ρ₀/(1+(r/r_c)²)`. -/
theorem dm_profile_boxed {rc r ρ₀ : ℝ} (hrc : 0 < rc) (hr : 0 ≤ r) :
    ρ₀ * rc^2 * ∫ b in Ioi r, b / (Real.sqrt (b^2 - r^2) * Real.sqrt (b^2 + rc^2)^3) =
      ρ₀ / (1 + (r/rc)^2) := by
  rw [abel_inverse_eval hrc hr, mul_one_div, mul_div_assoc,
    pseudo_isothermal_eq hrc r, mul_one_div]

end GppHalo
