/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.SchwartzTateLocal

/-!
# The Schwartz Tate local functional equation (L1)

For every Schwartz function `f : 𝓢(ℝ, ℂ)`, both characters `a ∈ {0, 1}` and every `s` in
the strip `0 < Re s < 1`,

  `Γℝ(s + a) Zₐ(𝓕 f, 1 - s) = (-i)^a Γℝ(1 - s + a) Zₐ(f, s)`,

with `Zₐ = parityZeta a`, Lebesgue measure, the kernel `e^(-2πixy)` and no factor of one
half (`localFE_schwartz_cross`); equivalently `Zₐ(𝓕 f, 1 - s) = γ(s, a) Zₐ(f, s)`
(`localFE_schwartz_ratio`).

**Route: Gaussian subordination.** Write `Γℝ(s + a) sign(x)^a |x|^(-s)` as
`∫₀^∞ t^((s+a)/2 - 1) x^a e^(-π t x²) dt`, swap (kernel `K₁`), pair `𝓕 f` against the
Gaussian (or `x` times it) by Parseval, use the Gaussian Fourier transform, and swap back
(kernel `K₂`), where the inverse subordination `∫₀^∞ t^(-b-1) e^(-π y²/t) dt` returns
`Γℝ(1 - s + a) sign(y)^a |y|^(s-1)`. Both swaps are product-absolutely integrable on the
open strip (`integrable_K1`, `integrable_K2` and their odd versions), with norm profiles
controlled by W1/W2; no regularization or limit is involved. The raw kernel
`f(x) e^(-2πixy) |y|^(-s)` is never used.

The proof uses only continuity and rapid decay of `f` and `𝓕 f` (`RapidDecay`), so the
equation is proved for that class (`localFE_cross_of_rapidDecay`) and the Schwartz
statements are corollaries. The #513 test vectors decay rapidly (`testVector_rapidDecay`),
and specializing recovers #513's `localFE_testVector`, proved there by direct evaluation
(`localFE_testVector_of_general`): an independent control on factors, phases and
normalization. This stands in for the statement sheet's T1/T2, which asked for a Gaussian
`SchwartzMap`; no such map exists in Mathlib, and the rapid-decay class makes it unneeded.

Governing specification: Principal series's Schwartz Tate statement sheet (GPP-bridge
`5fa0d320`, obligations L1, X1, X2, T1, T2), audited PASS by Turbo (`1d8e695`).
-/

open MeasureTheory Complex Asymptotics Filter Set
open scoped Topology FourierTransform SchwartzMap

namespace LocalTate.Archimedean

/-- Continuous and `O(‖x‖^r)` at infinity for every real `r`. Every Schwartz function
qualifies; the local FE below is proved under this hypothesis on `f` and `𝓕 f`. -/
def RapidDecay (g : ℝ → ℂ) : Prop :=
  Continuous g ∧ ∀ r : ℝ, g =O[cocompact ℝ] (‖·‖ ^ r)

theorem _root_.SchwartzMap.rapidDecay (g : 𝓢(ℝ, ℂ)) : RapidDecay g :=
  ⟨g.continuous, g.isBigO_cocompact_rpow⟩

theorem RapidDecay.integrable {g : ℝ → ℂ} (hg : RapidDecay g) : Integrable g := by
  have h := integrable_parityZeta_of_rapid_decay hg.1 hg.2 0 (s := 1) (by simp)
  simpa using h

/-- `(1/(π x²))^z = π^(-z) |x|^(-2z)` for `x ≠ 0`. -/
theorem one_div_pi_sq_cpow {x : ℝ} (hx : x ≠ 0) (z : ℂ) :
    (((1 / (Real.pi * x ^ 2) : ℝ)) : ℂ) ^ z =
      (Real.pi : ℂ) ^ (-z) * ((|x| : ℝ) : ℂ) ^ (-(2 * z)) := by
  have hax : 0 < |x| := abs_pos.mpr hx
  have hpi : 0 < Real.pi := Real.pi_pos
  have h1 : (1 / (Real.pi * x ^ 2) : ℝ) = Real.pi⁻¹ * (|x|⁻¹ * |x|⁻¹) := by
    rw [← sq_abs x]; field_simp
  rw [h1, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_mul,
    mul_cpow_ofReal_nonneg (by positivity) (by positivity), ofReal_inv, ofReal_inv,
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hpi.le]; exact hpi.ne),
    inv_cpow _ _ (by rw [arg_ofReal_of_nonneg hax.le]; exact hpi.ne), ← cpow_neg, ← cpow_neg,
    show -(2 * z) = -z + -z by ring, cpow_add _ _ (ofReal_ne_zero.mpr hax.ne')]

/-- Parseval for integrable functions on `ℝ`. -/
theorem integral_fourier_mul_flip {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
    Real.continuous_fourierChar continuous_inner hf hg
  have hflip : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
    ext; simp
  rw [hflip] at h
  exact h

/-- Real form of `one_div_pi_sq_cpow`. -/
theorem one_div_pi_sq_rpow {x : ℝ} (hx : x ≠ 0) (z : ℝ) :
    (1 / (Real.pi * x ^ 2)) ^ z = Real.pi ^ (-z) * |x| ^ (-(2 * z)) := by
  have h := one_div_pi_sq_cpow hx (z : ℂ)
  rw [← ofReal_cpow (by positivity), ← ofReal_neg, ← ofReal_cpow Real.pi_pos.le,
    show -(2 * (z : ℂ)) = ((-(2 * z) : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (abs_nonneg x), ← ofReal_mul] at h
  exact_mod_cast h

/-- Gaussian subordination: `∫₀^∞ t^(a-1) e^(-π x² t) dt = π^(-a) |x|^(-2a) Γ(a)`. -/
theorem subord_integral {x : ℝ} (hx : x ≠ 0) {a : ℂ} (ha : 0 < a.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (a - 1) * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t)) =
      (Real.pi : ℂ) ^ (-a) * ((|x| : ℝ) : ℂ) ^ (-(2 * a)) * Gamma a := by
  have hr : 0 < Real.pi * x ^ 2 := by positivity
  rw [integral_cpow_mul_exp_neg_mul_Ioi ha hr, ← one_div_pi_sq_cpow hx]
  push_cast; rfl

theorem subord_value_ne_zero {x : ℝ} (hx : x ≠ 0) {a : ℂ} (ha : 0 < a.re) :
    (Real.pi : ℂ) ^ (-a) * ((|x| : ℝ) : ℂ) ^ (-(2 * a)) * Gamma a ≠ 0 := by
  have hax : 0 < |x| := abs_pos.mpr hx
  refine mul_ne_zero (mul_ne_zero ?_ ?_) (Gamma_ne_zero_of_re_pos ha)
  · exact cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  · exact cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hax.ne'))

theorem subord_integrableOn {x : ℝ} (hx : x ≠ 0) {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) *
      cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [subord_integral hx ha]
  exact subord_value_ne_zero hx ha

/-- Inverse subordination: `∫₀^∞ t^(-b-1) e^(-π y²/t) dt = π^(-b) |y|^(-2b) Γ(b)`. -/
theorem subord_inv_integral {y : ℝ} (hy : y ≠ 0) {b : ℂ} (hb : 0 < b.re) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-b - 1) * cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t)) =
      (Real.pi : ℂ) ^ (-b) * ((|y| : ℝ) : ℂ) ^ (-(2 * b)) * Gamma b := by
  rw [← subord_integral hy hb,
    ← integral_comp_rpow_Ioi _ (show (-1 : ℝ) ≠ 0 by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx : (0 : ℝ) < x := hx
  have hxc : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx.le]; exact Real.pi_pos.ne
  simp only [Real.rpow_neg_one, abs_neg, abs_one, one_mul, real_smul, ofReal_inv]
  rw [show (-1 : ℝ) - 1 = -2 by norm_num, inv_cpow _ _ harg, ← cpow_neg, div_inv_eq_mul,
    ofReal_cpow hx.le, show ((-2 : ℝ) : ℂ) = -2 by push_cast; ring,
    show -(-b - 1) = (b - 1) + 2 by ring, cpow_add _ _ hxc, mul_comm (((Real.pi * y ^ 2 : ℝ)) : ℂ)]
  have h2 : (x : ℂ) ^ (-2 : ℂ) * (x : ℂ) ^ (2 : ℂ) = 1 := by
    rw [← cpow_add _ _ hxc]; simp
  linear_combination ((x : ℂ) ^ (b - 1) * cexp (-((x : ℂ) * ((Real.pi * y ^ 2 : ℝ) : ℂ)))) * h2

theorem subord_inv_integrableOn {y : ℝ} (hy : y ≠ 0) {b : ℂ} (hb : 0 < b.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-b - 1) *
      cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [subord_inv_integral hy hb]
  exact subord_value_ne_zero hy hb

/-- Real subordination, from the complex one at real exponent. -/
theorem real_subord_integral {x : ℝ} (hx : x ≠ 0) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Ioi 0, t ^ (a - 1) * Real.exp (-(Real.pi * x ^ 2 * t)) =
      Real.pi ^ (-a) * |x| ^ (-(2 * a)) * Real.Gamma a := by
  have h := subord_integral hx (a := (a : ℂ)) (by simpa using ha)
  have hc : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ ((a : ℂ) - 1) *
      cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t)) =
      ∫ t : ℝ in Ioi 0, ((t ^ (a - 1) * Real.exp (-(Real.pi * x ^ 2 * t)) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : (0 : ℝ) < t := ht
    simp [ofReal_cpow ht.le, ofReal_exp]
  rw [hc, integral_complex_ofReal] at h
  apply ofReal_injective
  rw [h, ofReal_mul, ofReal_mul, ofReal_cpow Real.pi_pos.le, ofReal_cpow (abs_nonneg x),
    Gamma_ofReal]
  push_cast; ring_nf

theorem real_subord_inv_integral {y : ℝ} (hy : y ≠ 0) {b : ℝ} (hb : 0 < b) :
    ∫ t : ℝ in Ioi 0, t ^ (-b - 1) * Real.exp (-(Real.pi * y ^ 2 / t)) =
      Real.pi ^ (-b) * |y| ^ (-(2 * b)) * Real.Gamma b := by
  have h := subord_inv_integral hy (b := (b : ℂ)) (by simpa using hb)
  have hc : ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-(b : ℂ) - 1) *
      cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t)) =
      ∫ t : ℝ in Ioi 0, ((t ^ (-b - 1) * Real.exp (-(Real.pi * y ^ 2 / t)) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht : (0 : ℝ) < t := ht
    simp [ofReal_cpow ht.le, ofReal_exp]
  rw [hc, integral_complex_ofReal] at h
  apply ofReal_injective
  rw [h, ofReal_mul, ofReal_mul, ofReal_cpow Real.pi_pos.le, ofReal_cpow (abs_nonneg y),
    Gamma_ofReal]
  push_cast; ring_nf

theorem norm_subord {t : ℝ} (ht : 0 < t) (r : ℝ) (a : ℂ) :
    ‖(t : ℂ) ^ (a - 1) * cexp (-((r : ℂ) * t))‖ = t ^ (a.re - 1) * Real.exp (-(r * t)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp

theorem norm_subord_inv {t : ℝ} (ht : 0 < t) (r : ℝ) (b : ℂ) :
    ‖(t : ℂ) ^ (-b - 1) * cexp (-((r : ℂ) / t))‖ = t ^ (-b.re - 1) * Real.exp (-(r / t)) := by
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, norm_exp]
  simp [← ofReal_div]

/-- Product integrability of `h(x) φ(x,t)` from section integrability and an integrable
norm profile. -/
theorem integrable_kernel {h : ℝ → ℂ} (hh : Continuous h) {φ : ℝ → ℝ → ℂ}
    (hφ : Measurable (fun p : ℝ × ℝ => φ p.1 p.2))
    (hint : ∀ x ≠ 0, IntegrableOn (φ x) (Ioi 0)) (c : ℝ → ℝ)
    (hnorm : ∀ x ≠ 0, ∫ t in Ioi 0, ‖φ x t‖ = c x)
    (hc : Integrable (fun x => ‖h x‖ * c x)) :
    Integrable (fun p : ℝ × ℝ => h p.1 * φ p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => h p.1 * φ p.1 p.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) :=
    ((hh.measurable.comp measurable_fst).mul hφ).aestronglyMeasurable
  refine (integrable_prod_iff hm).2 ⟨?_, ?_⟩
  · filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    exact (hint x hx).const_mul (h x)
  · refine hc.congr ?_
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    simp only [norm_mul]
    rw [integral_const_mul, hnorm x hx]

/-- The profile `‖g x‖ |x|^(-2c)` is integrable for Schwartz `g` and `0 < c < 1/2`. -/
theorem integrable_profile {g : ℝ → ℂ} (hg : RapidDecay g) {c : ℝ} (hc1 : c < 1 / 2) (K : ℝ) :
    Integrable (fun x : ℝ => ‖g x‖ * (Real.pi ^ (-c) * |x| ^ (-(2 * c)) * K)) := by
  have hw : 0 < (((1 - 2 * c : ℝ)) : ℂ).re := by simp; linarith
  refine ((integrable_parityZeta_of_rapid_decay hg.1 hg.2 0 hw).norm.mul_const (Real.pi ^ (-c) * K)).congr ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  have hax : 0 < |x| := abs_pos.mpr hx
  simp only [Fin.val_zero, pow_zero, mul_one, norm_mul]
  rw [norm_cpow_eq_rpow_re_of_pos hax]
  simp only [sub_re, ofReal_re, one_re]
  ring_nf

/-- Swap-1 kernel: product integrable for `0 < Re a < 1/2`. -/
theorem integrable_K1 {g : ℝ → ℂ} (hg : RapidDecay g) {a : ℂ} (ha : 0 < a.re) (ha1 : a.re < 1 / 2) :
    Integrable (fun p : ℝ × ℝ => g p.1 * ((p.2 : ℂ) ^ (a - 1) *
      cexp (-(((Real.pi * p.1 ^ 2 : ℝ) : ℂ) * p.2))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  refine integrable_kernel hg.1 (by fun_prop) (fun x hx => subord_integrableOn hx ha)
    (fun x => Real.pi ^ (-a.re) * |x| ^ (-(2 * a.re)) * Real.Gamma a.re) (fun x hx => ?_)
    (integrable_profile hg ha1 _)
  rw [← real_subord_integral hx ha]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_subord ht]

/-- Swap-2 kernel: product integrable for `0 < Re b < 1/2`. -/
theorem integrable_K2 {g : ℝ → ℂ} (hg : RapidDecay g) {b : ℂ} (hb : 0 < b.re) (hb1 : b.re < 1 / 2) :
    Integrable (fun p : ℝ × ℝ => g p.1 * ((p.2 : ℂ) ^ (-b - 1) *
      cexp (-(((Real.pi * p.1 ^ 2 : ℝ) : ℂ) / p.2))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  refine integrable_kernel hg.1 (by fun_prop) (fun x hx => subord_inv_integrableOn hx hb)
    (fun x => Real.pi ^ (-b.re) * |x| ^ (-(2 * b.re)) * Real.Gamma b.re) (fun x hx => ?_)
    (integrable_profile hg hb1 _)
  rw [← real_subord_inv_integral hx hb]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_subord_inv ht]

/-- Fourier transform of the subordinated Gaussian, paired against `𝓕 f`. -/
theorem fourier_pair_gaussian {f : ℝ → ℂ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    ∫ x, 𝓕 (f : ℝ → ℂ) x * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t)) =
      ∫ y, f y * (1 / (t : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi / t * y ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have hG : (fun x : ℝ => cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) =
      fun x : ℝ => cexp (-Real.pi * t * x ^ 2) := by
    funext x; congr 1; push_cast; ring
  have hGi : Integrable (fun x : ℝ => cexp (-Real.pi * t * x ^ 2)) := by
    have := integrable_cexp_neg_mul_sq (b := (Real.pi : ℂ) * t)
      (by simpa using mul_pos Real.pi_pos ht)
    simpa [neg_mul] using this
  rw [← hG] at hGi
  have h := integral_fourier_mul_flip hf hGi
  rw [hG, fourier_gaussian_pi htc] at h
  exact h

/-- **L1, even character.** For every Schwartz `f` and `0 < Re s < 1`,
`Γℝ(s) Z₀(𝓕 f, 1 - s) = Γℝ(1 - s) Z₀(f, s)`. -/
theorem localFE_even_of_rapidDecay {f : ℝ → ℂ} (hf : RapidDecay f)
    (hF : RapidDecay (𝓕 f)) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Gammaℝ s * parityZeta 0 (𝓕 (f : ℝ → ℂ)) (1 - s) =
      Gammaℝ (1 - s) * parityZeta 0 f s := by
  have ha : 0 < (s / 2).re := by simp; linarith
  have ha1 : (s / 2).re < 1 / 2 := by simp; linarith
  have hb : 0 < ((1 - s) / 2).re := by simp; linarith
  have hb1 : ((1 - s) / 2).re < 1 / 2 := by simp; linarith
  -- Step A: subordinate `|x|^(-s)`.
  have hA : Gammaℝ s * parityZeta 0 (𝓕 (f : ℝ → ℂ)) (1 - s) =
      ∫ x, ∫ t : ℝ in Ioi 0, (𝓕 f : ℝ → ℂ) x * ((t : ℂ) ^ (s / 2 - 1) *
        cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) := by
    unfold parityZeta
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [integral_const_mul, subord_integral hx ha]
    simp only [Fin.val_zero, pow_zero, mul_one, Gammaℝ]
    rw [show (1 - s) - 1 = -s by ring, show -(2 * (s / 2)) = -s by ring,
      show -s / 2 = -(s / 2) by ring]
    ring
  -- Step C: the inner `x`-integral, for fixed `t > 0`.
  have hC : ∀ t ∈ Ioi (0 : ℝ),
      ∫ x, (𝓕 f : ℝ → ℂ) x * ((t : ℂ) ^ (s / 2 - 1) *
        cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) =
      ∫ y, f y * ((t : ℂ) ^ (-((1 - s) / 2) - 1) *
        cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t))) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    calc _ = (t : ℂ) ^ (s / 2 - 1) * ∫ x, (𝓕 f : ℝ → ℂ) x *
          cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t)) := by
            rw [← integral_const_mul]; congr 1; funext x; ring
      _ = (t : ℂ) ^ (s / 2 - 1) * ∫ y, f y *
          (1 / (t : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi / t * y ^ 2)) := by
            rw [fourier_pair_gaussian hf.integrable ht]
      _ = _ := by
            rw [← integral_const_mul]; congr 1; funext y
            rw [show (t : ℂ) ^ (-((1 - s) / 2) - 1) = (t : ℂ) ^ (s / 2 - 1) / (t : ℂ) ^ (1 / 2 : ℂ) by
              rw [← cpow_sub _ _ htc]; ring_nf]
            have he : cexp (-Real.pi / t * y ^ 2) =
                cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t)) := by
              congr 1; push_cast; ring
            rw [he]; field_simp
  rw [hA, integral_integral_swap (f := fun (x t : ℝ) => (𝓕 f : ℝ → ℂ) x * ((t : ℂ) ^ (s / 2 - 1) *
        cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t)))) (integrable_K1 hF ha ha1),
    setIntegral_congr_fun measurableSet_Ioi hC,
    ← integral_integral_swap (f := fun (y t : ℝ) => f y * ((t : ℂ) ^ (-((1 - s) / 2) - 1) *
        cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t)))) (integrable_K2 hf hb hb1)]
  -- Step E: evaluate the inverse subordination.
  unfold parityZeta
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
  rw [integral_const_mul, subord_inv_integral hy hb]
  simp only [Fin.val_zero, pow_zero, mul_one, Gammaℝ]
  rw [show -(2 * ((1 - s) / 2)) = s - 1 by ring, show -(1 - s) / 2 = -((1 - s) / 2) by ring]
  ring

/-! ### Odd character -/

/-- Fourier transform of `x e^(-π t x²)`: `-i y t^(-3/2) e^(-π y²/t)`. -/
theorem fourier_x_gaussian {t : ℝ} (ht : 0 < t) :
    𝓕 (fun x : ℝ => (x : ℂ) * cexp (-Real.pi * t * x ^ 2)) =
      fun y : ℝ => -I * y / t * (1 / (t : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi / t * y ^ 2)) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  have hb : 0 < ((Real.pi : ℂ) * t).re := by simpa using mul_pos Real.pi_pos ht
  set G : ℝ → ℂ := fun x => cexp (-Real.pi * t * x ^ 2) with hGdef
  have hG' : ∀ x : ℝ, HasDerivAt G (-2 * Real.pi * t * x * G x) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => (-Real.pi * t * (x : ℂ) ^ 2)) (-Real.pi * t * (2 * x)) x := by
      have := ((hasDerivAt_id (x : ℂ)).pow 2).const_mul (-Real.pi * (t : ℂ))
      simpa using this.comp_ofReal
    convert h1.cexp using 1
    simp [G]; ring
  have hderiv : deriv G = fun x : ℝ => (-2 * Real.pi * t : ℂ) • ((x : ℂ) * G x) := by
    funext x; rw [(hG' x).deriv]; simp [smul_eq_mul]; ring
  have hGi : Integrable G := by
    simpa [G, neg_mul] using integrable_cexp_neg_mul_sq hb
  have hxGi : Integrable (fun x : ℝ => (x : ℂ) * G x) := by
    simpa [G, neg_mul] using integrable_mul_cexp_neg_mul_sq hb
  have hD : Integrable (deriv G) := by rw [hderiv]; exact hxGi.const_mul _
  have hdiff : Differentiable ℝ G := fun x => (hG' x).differentiableAt
  have hF := Real.fourier_deriv hGi hdiff hD
  rw [hderiv] at hF
  have hc : (-2 * Real.pi * t : ℂ) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    have : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp_all
  have hsmul : 𝓕 (fun x : ℝ => (-2 * Real.pi * t : ℂ) • ((x : ℂ) * G x)) =
      (-2 * Real.pi * t : ℂ) • 𝓕 (fun x : ℝ => (x : ℂ) * G x) :=
    VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) _ _
  rw [hsmul, fourier_gaussian_pi htc] at hF
  change 𝓕 (fun x : ℝ => (x : ℂ) * G x) = _
  funext y
  have hy := congrFun hF y
  simp only [Pi.smul_apply, smul_eq_mul] at hy
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have htc' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  field_simp at hy ⊢
  linear_combination -hy

/-- `x |x|^(-(w+1)) = sign(x) |x|^(-w)` for `x ≠ 0`. -/
theorem mul_abs_cpow_neg_succ {x : ℝ} (hx : x ≠ 0) (w : ℂ) :
    (x : ℂ) * ((|x| : ℝ) : ℂ) ^ (-(w + 1)) = (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) ^ (-w) := by
  have hax : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (abs_ne_zero.mpr hx)
  have hxs : (x : ℂ) = (Real.sign x : ℂ) * ((|x| : ℝ) : ℂ) := by
    have : x = Real.sign x * |x| := by
      obtain hn | rfl | hp := lt_trichotomy x 0
      · rw [Real.sign_of_neg hn, abs_of_neg hn]; ring
      · exact absurd rfl hx
      · rw [Real.sign_of_pos hp, abs_of_pos hp]; ring
    exact_mod_cast this
  rw [neg_add, cpow_add _ _ hax, cpow_neg_one, hxs]
  field_simp

theorem integrable_profile_odd {g : ℝ → ℂ} (hg : RapidDecay g) {c : ℝ} (hc1 : c < 1) (K : ℝ) :
    Integrable (fun x : ℝ => ‖(x : ℂ) * g x‖ * (Real.pi ^ (-c) * |x| ^ (-(2 * c)) * K)) := by
  have hw : 0 < (((2 - 2 * c : ℝ)) : ℂ).re := by simp; linarith
  refine ((integrable_parityZeta_of_rapid_decay hg.1 hg.2 0 hw).norm.mul_const (Real.pi ^ (-c) * K)).congr ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
  have hax : 0 < |x| := abs_pos.mpr hx
  simp only [Fin.val_zero, pow_zero, mul_one, norm_mul, norm_real, Real.norm_eq_abs]
  rw [norm_cpow_eq_rpow_re_of_pos hax]
  simp only [sub_re, ofReal_re, one_re]
  rw [show 2 - 2 * c - 1 = 1 + -(2 * c) by ring, Real.rpow_add hax, Real.rpow_one]
  ring

theorem integrable_K1_odd {g : ℝ → ℂ} (hg : RapidDecay g) {a : ℂ} (ha : 0 < a.re) (ha1 : a.re < 1) :
    Integrable (fun p : ℝ × ℝ => ((p.1 : ℂ) * g p.1) * ((p.2 : ℂ) ^ (a - 1) *
      cexp (-(((Real.pi * p.1 ^ 2 : ℝ) : ℂ) * p.2))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  refine integrable_kernel (continuous_ofReal.mul hg.1) (by fun_prop)
    (fun x hx => subord_integrableOn hx ha)
    (fun x => Real.pi ^ (-a.re) * |x| ^ (-(2 * a.re)) * Real.Gamma a.re) (fun x hx => ?_)
    (integrable_profile_odd hg ha1 _)
  rw [← real_subord_integral hx ha]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_subord ht]

theorem integrable_K2_odd {g : ℝ → ℂ} (hg : RapidDecay g) {b : ℂ} (hb : 0 < b.re) (hb1 : b.re < 1) :
    Integrable (fun p : ℝ × ℝ => ((p.1 : ℂ) * g p.1) * ((p.2 : ℂ) ^ (-b - 1) *
      cexp (-(((Real.pi * p.1 ^ 2 : ℝ) : ℂ) / p.2))))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
  refine integrable_kernel (continuous_ofReal.mul hg.1) (by fun_prop)
    (fun x hx => subord_inv_integrableOn hx hb)
    (fun x => Real.pi ^ (-b.re) * |x| ^ (-(2 * b.re)) * Real.Gamma b.re) (fun x hx => ?_)
    (integrable_profile_odd hg hb1 _)
  rw [← real_subord_inv_integral hx hb]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [norm_subord_inv ht]

theorem fourier_pair_x_gaussian {f : ℝ → ℂ} (hf : Integrable f) {t : ℝ} (ht : 0 < t) :
    ∫ x, 𝓕 (f : ℝ → ℂ) x * ((x : ℂ) * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) =
      ∫ y, f y * (-I * y / t * (1 / (t : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi / t * y ^ 2))) := by
  have hb : 0 < ((Real.pi : ℂ) * t).re := by simpa using mul_pos Real.pi_pos ht
  have hG : (fun x : ℝ => (x : ℂ) * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) =
      fun x : ℝ => (x : ℂ) * cexp (-Real.pi * t * x ^ 2) := by
    funext x; congr 2; push_cast; ring
  have hGi : Integrable (fun x : ℝ => (x : ℂ) * cexp (-Real.pi * t * x ^ 2)) := by
    simpa [neg_mul] using integrable_mul_cexp_neg_mul_sq hb
  rw [← hG] at hGi
  have h := integral_fourier_mul_flip hf hGi
  rw [hG, fourier_x_gaussian ht] at h
  exact h

/-- **L1, odd character.** For every Schwartz `f` and `0 < Re s < 1`,
`Γℝ(s + 1) Z₁(𝓕 f, 1 - s) = -i Γℝ(2 - s) Z₁(f, s)`. -/
theorem localFE_odd_of_rapidDecay {f : ℝ → ℂ} (hf : RapidDecay f)
    (hF : RapidDecay (𝓕 f)) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Gammaℝ (s + 1) * parityZeta 1 (𝓕 (f : ℝ → ℂ)) (1 - s) =
      -I * Gammaℝ (1 - s + 1) * parityZeta 1 f s := by
  have ha : 0 < ((s + 1) / 2).re := by simp; linarith
  have ha1 : ((s + 1) / 2).re < 1 := by simp; linarith
  have hb : 0 < ((1 - s + 1) / 2).re := by simp; linarith
  have hb1 : ((1 - s + 1) / 2).re < 1 := by simp; linarith
  have hA : Gammaℝ (s + 1) * parityZeta 1 (𝓕 (f : ℝ → ℂ)) (1 - s) =
      ∫ x : ℝ, ∫ t : ℝ in Ioi 0, ((x : ℂ) * (𝓕 f : ℝ → ℂ) x) * ((t : ℂ) ^ ((s + 1) / 2 - 1) *
        cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) := by
    unfold parityZeta
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
    rw [integral_const_mul, subord_integral hx ha]
    simp only [Fin.val_one, pow_one, Gammaℝ]
    rw [show -(2 * ((s + 1) / 2)) = -(s + 1) by ring, show -(s + 1) / 2 = -((s + 1) / 2) by ring,
      show (1 - s) - 1 = -s by ring]
    have h := mul_abs_cpow_neg_succ hx s
    linear_combination -((Real.pi : ℂ) ^ (-((s + 1) / 2)) * Gamma ((s + 1) / 2) *
      𝓕 (f : ℝ → ℂ) x) * h
  have hC : ∀ t ∈ Ioi (0 : ℝ),
      ∫ x : ℝ, ((x : ℂ) * (𝓕 f : ℝ → ℂ) x) * ((t : ℂ) ^ ((s + 1) / 2 - 1) *
        cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) =
      -I * ∫ y : ℝ, ((y : ℂ) * f y) * ((t : ℂ) ^ (-((1 - s + 1) / 2) - 1) *
        cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t))) := by
    intro t ht
    have ht : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    calc _ = (t : ℂ) ^ ((s + 1) / 2 - 1) * ∫ x, (𝓕 f : ℝ → ℂ) x *
          ((x : ℂ) * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))) := by
            rw [← integral_const_mul]; congr 1; funext x; ring
      _ = (t : ℂ) ^ ((s + 1) / 2 - 1) * ∫ y, f y *
          (-I * y / t * (1 / (t : ℂ) ^ (1 / 2 : ℂ) * cexp (-Real.pi / t * y ^ 2))) := by
            rw [fourier_pair_x_gaussian hf.integrable ht]
      _ = _ := by
            rw [← integral_const_mul, ← integral_const_mul]; congr 1; funext y
            rw [show (t : ℂ) ^ (-((1 - s + 1) / 2) - 1) =
                (t : ℂ) ^ ((s + 1) / 2 - 1) / (t : ℂ) / (t : ℂ) ^ (1 / 2 : ℂ) by
              rw [show -((1 - s + 1) / 2) - 1 = ((s + 1) / 2 - 1 - 1) - 1 / 2 by ring,
                cpow_sub _ _ htc, cpow_sub _ _ htc, cpow_one]]
            have he : cexp (-Real.pi / t * y ^ 2) =
                cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t)) := by
              congr 1; push_cast; ring
            rw [he]; field_simp
  rw [hA, integral_integral_swap (f := fun (x t : ℝ) => ((x : ℂ) * (𝓕 f : ℝ → ℂ) x) *
        ((t : ℂ) ^ ((s + 1) / 2 - 1) * cexp (-(((Real.pi * x ^ 2 : ℝ) : ℂ) * t))))
      (integrable_K1_odd hF ha ha1),
    setIntegral_congr_fun measurableSet_Ioi hC, integral_const_mul,
    ← integral_integral_swap (f := fun (y t : ℝ) => ((y : ℂ) * f y) *
        ((t : ℂ) ^ (-((1 - s + 1) / 2) - 1) * cexp (-(((Real.pi * y ^ 2 : ℝ) : ℂ) / t))))
      (integrable_K2_odd hf hb hb1)]
  unfold parityZeta
  rw [mul_assoc]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [volume.ae_ne (0 : ℝ)] with y hy
  rw [integral_const_mul, subord_inv_integral hy hb]
  simp only [Fin.val_one, pow_one, Gammaℝ]
  rw [show -(2 * ((1 - s + 1) / 2)) = -((1 - s) + 1) by ring,
    show -(1 - s + 1) / 2 = -((1 - s + 1) / 2) by ring]
  have h := mul_abs_cpow_neg_succ hy (1 - s)
  rw [show -(1 - s) = s - 1 by ring] at h
  linear_combination (Real.pi : ℂ) ^ (-((1 - s + 1) / 2)) * Gamma ((1 - s + 1) / 2) * f y * h

/-- **L1** under rapid decay of `f` and `𝓕 f`, cross-multiplied, both characters:
`Aₐ(s) Zₐ(𝓕 f, 1 - s) = cₐ Aₐ(1 - s) Zₐ(f, s)` on `0 < Re s < 1`. -/
theorem localFE_cross_of_rapidDecay {f : ℝ → ℂ} (hf : RapidDecay f) (hF : RapidDecay (𝓕 f))
    (a : Fin 2) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    archFactor a s * parityZeta a (𝓕 (f : ℝ → ℂ)) (1 - s) =
      archPhase a * archFactor a (1 - s) * parityZeta a f s := by
  rcases (show a = 0 ∨ a = 1 by fin_cases a <;> decide) with rfl | rfl
  · simpa [archFactor, archPhase] using localFE_even_of_rapidDecay hf hF hs0 hs1
  · simpa [archFactor, archPhase] using localFE_odd_of_rapidDecay hf hF hs0 hs1

/-- **L1, ratio form.** `Zₐ(𝓕 f, 1 - s) = γ(s, a) Zₐ(f, s)` on `0 < Re s < 1`. -/
theorem localFE_ratio_of_rapidDecay {f : ℝ → ℂ} (hf : RapidDecay f) (hF : RapidDecay (𝓕 f))
    (a : Fin 2) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    parityZeta a (𝓕 f) (1 - s) = gammaRatio a s * parityZeta a f s :=
  ratio_of_cross a (archFactor_ne_zero_strip a hs0 hs1).1
    (localFE_cross_of_rapidDecay hf hF a hs0 hs1)

/-! ### The Schwartz statements -/

theorem fourier_rapidDecay (f : 𝓢(ℝ, ℂ)) : RapidDecay (𝓕 (f : ℝ → ℂ)) := by
  rw [← SchwartzMap.fourier_coe]; exact (𝓕 f).rapidDecay

/-- **L1.** The Schwartz local functional equation, cross-multiplied, both characters. -/
theorem localFE_schwartz_cross (f : 𝓢(ℝ, ℂ)) (a : Fin 2) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    archFactor a s * parityZeta a (𝓕 (f : ℝ → ℂ)) (1 - s) =
      archPhase a * archFactor a (1 - s) * parityZeta a f s :=
  localFE_cross_of_rapidDecay f.rapidDecay (fourier_rapidDecay f) a hs0 hs1

/-- **L1, ratio form.** `Zₐ(𝓕 f, 1 - s) = γ(s, a) Zₐ(f, s)` on `0 < Re s < 1`. -/
theorem localFE_schwartz_ratio (f : 𝓢(ℝ, ℂ)) (a : Fin 2) {s : ℂ} (hs0 : 0 < s.re)
    (hs1 : s.re < 1) :
    parityZeta a (𝓕 (f : ℝ → ℂ)) (1 - s) = gammaRatio a s * parityZeta a f s :=
  localFE_ratio_of_rapidDecay f.rapidDecay (fourier_rapidDecay f) a hs0 hs1

/-! ### T1/T2: recovery of the #513 test-vector equation -/

/-- **T1.** The two #513 test vectors `x^a e^(-πx²)` are rapidly decaying. -/
theorem testVector_rapidDecay (a : Fin 2) : RapidDecay (testVector a) := by
  refine ⟨by unfold testVector gaussian; fun_prop, fun r => ?_⟩
  set u : ℝ → ℝ := fun y => y ^ (a.val : ℝ) * Real.exp (-Real.pi * y ^ 2)
  have hu : u =O[atTop] (· ^ r) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg Real.pi_pos _).isBigO.trans
      (isLittleO_exp_neg_mul_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2) r).isBigO
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)).trans
    (hu.comp_tendsto tendsto_norm_cocompact_atTop)
  simp only [Function.comp_apply, u, testVector, gaussian, norm_mul, norm_pow, norm_real,
    Real.norm_eq_abs, one_mul, Real.rpow_natCast, sq_abs, abs_abs,
    Real.abs_exp]
  rfl

/-- **T1.** Their Fourier transforms (`archPhase a • testVector a`) are rapidly decaying. -/
theorem fourier_testVector_rapidDecay (a : Fin 2) : RapidDecay (𝓕 (testVector a)) := by
  rw [fourier_testVector]
  obtain ⟨hc, hd⟩ := testVector_rapidDecay a
  exact ⟨continuous_const.mul hc, fun r => (hd r).const_mul_left _⟩

/-- **T2.** The general local FE specializes to #513's `localFE_testVector`: same factors,
same phases `+1` and `-i`, same normalization. The two proofs are independent (#513
evaluates both sides; this one is Gaussian subordination), so agreement is a regression
control on conventions. -/
theorem localFE_testVector_of_general (a : Fin 2) {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    archFactor a s * parityZeta a (𝓕 (testVector a)) (1 - s) =
      archPhase a * archFactor a (1 - s) * parityZeta a (testVector a) s :=
  localFE_cross_of_rapidDecay (testVector_rapidDecay a) (fourier_testVector_rapidDecay a)
    a hs0 hs1

end LocalTate.Archimedean
