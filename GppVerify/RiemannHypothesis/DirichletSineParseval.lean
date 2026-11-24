/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude)
-/
import Mathlib.Tactic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Dirichlet sine system on `(0, L]`: Parseval and polarised Parseval

Infrastructure for the undamping operator items (b)/(c) (Turbo's decision 2026-11-21: build the
basis infrastructure). Mathlib has `fourierBasis` on `AddCircle` but no Dirichlet-sine system; this
file derives sine Parseval from Mathlib's interval Parseval (`hasSum_sq_fourierCoeffOn`) by odd
extension to `(−L, L]`.

* `oddExt g`: odd extension of `g` (`g` is only read on `(0, L]`).
* `coeff_odd`: for `n : ℤ`, the Fourier integral of `oddExt g` on `[−L, L]` equals
  `−2i · ∫₀ᴸ sin(nπx/L) g(x) dx`.
* `sine_parseval`: for bounded measurable `g : ℝ → ℂ`,
  `Σₙ (2/L) ‖∫₀ᴸ sin(nπx/L) g‖² = ∫₀ᴸ ‖g‖²`.
* `sine_parseval_real`, `sine_parseval_pol`: the real-valued forms; the latter is the polarised
  identity `∫₀ᴸ f g = (2/L) Σₙ cₙ(f) cₙ(g)`, `cₙ(f) = rc L f n = ∫₀ᴸ sin(nπx/L) f(x) dx`.

Scope: bounded measurable functions (all that the quadratic-form statements need); this is the
statement "the Dirichlet sines are a complete orthogonal system" at the level of Parseval, not a
`HilbertBasis` of `Lp`. No `sorry`, no `axiom`.
-/


open MeasureTheory Set Complex

namespace GppSineBasis

/-- Odd extension of `g` (defined on `(0,L]`) to `ℝ`. -/
noncomputable def oddExt (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then g x else if x < 0 then - g (-x) else 0

theorem oddExt_neg (g : ℝ → ℂ) (x : ℝ) : oddExt g (-x) = - oddExt g x := by
  unfold oddExt
  rcases lt_trichotomy x 0 with h | h | h
  · have h1 : ¬ (0 < x) := not_lt.mpr h.le
    have h2 : 0 < -x := by linarith
    simp [h1, h, h2]
  · subst h; simp
  · have h1 : ¬ (0 < -x) := by linarith
    have h2 : -x < 0 := by linarith
    simp [h1, h, h2]

theorem oddExt_bound {g : ℝ → ℂ} {B : ℝ} (hB : ∀ x, ‖g x‖ ≤ B) (hB0 : 0 ≤ B) (x : ℝ) :
    ‖oddExt g x‖ ≤ B := by
  unfold oddExt
  split_ifs
  · exact hB x
  · simpa using hB (-x)
  · simpa using hB0

theorem oddExt_measurable {g : ℝ → ℂ} (hg : Measurable g) : Measurable (oddExt g) := by
  unfold oddExt
  refine Measurable.ite measurableSet_Ioi hg ?_
  refine Measurable.ite measurableSet_Iio (hg.comp measurable_neg).neg measurable_const

theorem ii_of_bound {h : ℝ → ℂ} (hh : Measurable h) {B : ℝ} (hb : ∀ x, ‖h x‖ ≤ B) (a b : ℝ) :
    IntervalIntegrable h volume a b := by
  have : IntegrableOn h (uIoc a b) volume :=
    Measure.integrableOn_of_bounded (by simp [Real.volume_uIoc]) hh.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  exact (intervalIntegrable_iff.mpr this)

theorem ii_of_bound' {h : ℝ → ℝ} (hh : Measurable h) {B : ℝ} (hb : ∀ x, ‖h x‖ ≤ B) (a b : ℝ) :
    IntervalIntegrable h volume a b := by
  have : IntegrableOn h (uIoc a b) volume :=
    Measure.integrableOn_of_bounded (by simp [Real.volume_uIoc]) hh.aestronglyMeasurable
      (Filter.Eventually.of_forall hb)
  exact (intervalIntegrable_iff.mpr this)

/-- `∫₀ᴸ sin(nπx/L) g(x) dx`. -/
noncomputable def sinCoeff (L : ℝ) (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..L, ((Real.sin (n * Real.pi * x / L) : ℝ) : ℂ) * g x

theorem coeff_odd {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) (n : ℤ) :
    ∫ x in (-L)..L, Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((L - -L : ℝ) : ℂ))
        * oddExt g x
      = -2 * Complex.I * ∫ x in (0 : ℝ)..L, ((Real.sin (n * Real.pi * x / L) : ℝ) : ℂ) * g x := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  set e : ℝ → ℂ := fun x => Complex.exp (-(((n * Real.pi * x / L : ℝ)) : ℂ) * Complex.I) with he
  have hE : ∀ x : ℝ, Complex.exp (2 * Real.pi * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((L - -L : ℝ) : ℂ))
      = e x := by
    intro x
    simp only [he]
    congr 1
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  simp_rw [hE]
  have hec : Continuous e := by simp only [he]; fun_prop
  have hen : ∀ x, ‖e x‖ = 1 := by
    intro x; simp only [he]
    rw [Complex.norm_exp]; simp
  have hGm := oddExt_measurable hg
  have hGb := oddExt_bound hB hB0
  have iF : ∀ a b : ℝ, IntervalIntegrable (fun x => e x * oddExt g x) volume a b := fun a b =>
    ii_of_bound (B := B) (hec.measurable.mul hGm) (fun x => by
      show ‖e x * oddExt g x‖ ≤ B
      rw [norm_mul, hen, one_mul]; exact hGb x) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (iF (-L) 0) (iF 0 L)]
  -- right half
  have hR : ∫ x in (0 : ℝ)..L, e x * oddExt g x = ∫ x in (0 : ℝ)..L, e x * g x := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hL.le] at hx
    simp only [oddExt, if_pos hx.1]
  -- left half
  have hLf : ∫ x in (-L)..0, e x * oddExt g x = ∫ u in (0 : ℝ)..L, e (-u) * (-g u) := by
    have hae : ∀ᵐ x : ℝ, x ∈ uIoc (-L) 0 → e x * oddExt g x = e x * (-g (-x)) := by
      have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by rw [ae_iff]; simp
      filter_upwards [h0] with x hx0 hx
      rw [uIoc_of_le (by linarith)] at hx
      have : x < 0 := lt_of_le_of_ne hx.2 hx0
      simp only [oddExt, if_neg (not_lt.mpr this.le), if_pos this]
    rw [intervalIntegral.integral_congr_ae hae]
    have := intervalIntegral.integral_comp_neg (a := -L) (b := 0) (fun u => e (-u) * (-g u))
    simp only [neg_neg, neg_zero] at this
    exact this
  rw [hLf, hR]
  have iA : IntervalIntegrable (fun u => e (-u) * (-g u)) volume 0 L :=
    ii_of_bound (B := B) ((hec.comp continuous_neg).measurable.mul hg.neg) (fun x => by
      show ‖e (-x) * (-g x)‖ ≤ B
      rw [norm_mul, hen, one_mul, norm_neg]; exact hB x) 0 L
  have iB : IntervalIntegrable (fun u => e u * g u) volume 0 L :=
    ii_of_bound (B := B) (hec.measurable.mul hg) (fun x => by
      show ‖e x * g x‖ ≤ B
      rw [norm_mul, hen, one_mul]; exact hB x) 0 L
  rw [← intervalIntegral.integral_add iA iB, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp only [he]
  have hc : Complex.exp (-(((n * Real.pi * (-x) / L : ℝ)) : ℂ) * Complex.I)
      = Complex.exp ((((n * Real.pi * x / L : ℝ)) : ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  rw [hc]
  have hs : ((Real.sin (n * Real.pi * x / L) : ℝ) : ℂ)
      = (Complex.exp ((((n * Real.pi * x / L : ℝ)) : ℂ) * Complex.I)
        - Complex.exp (-(((n * Real.pi * x / L : ℝ)) : ℂ) * Complex.I)) / (2 * Complex.I) := by
    rw [Complex.ofReal_sin, Complex.sin]
    have : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    field_simp
    rw [Complex.I_sq]; ring
  rw [hs]
  field_simp
  ring

theorem sinCoeff_zero (L : ℝ) (g : ℝ → ℂ) : sinCoeff L g 0 = 0 := by
  simp [sinCoeff]

theorem norm_sq_odd {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) :
    ∫ x in (-L)..L, ‖oddExt g x‖ ^ 2 = 2 * ∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2 := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hGm := oddExt_measurable hg
  have hGb := oddExt_bound hB hB0
  have iF : ∀ a b : ℝ, IntervalIntegrable (fun x => ‖oddExt g x‖ ^ 2) volume a b := fun a b =>
    ii_of_bound' (B := B ^ 2) (by fun_prop) (fun x => by
      rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hGb x) 2) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (iF (-L) 0) (iF 0 L)]
  have hR : ∫ x in (0 : ℝ)..L, ‖oddExt g x‖ ^ 2 = ∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2 := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
    rw [uIoc_of_le hL.le] at hx
    simp only [oddExt, if_pos hx.1]
  have hLf : ∫ x in (-L)..0, ‖oddExt g x‖ ^ 2 = ∫ x in (0 : ℝ)..L, ‖oddExt g x‖ ^ 2 := by
    have := intervalIntegral.integral_comp_neg (a := -L) (b := 0) (fun u => ‖oddExt g u‖ ^ 2)
    simp only [neg_neg, neg_zero] at this
    rw [← this]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [oddExt_neg, norm_neg]
  rw [hLf, hR]; ring

theorem sine_parseval {L : ℝ} (hL : 0 < L) {g : ℝ → ℂ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) :
    HasSum (fun n : ℕ => (2 / L) * ‖sinCoeff L g n‖ ^ 2) (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hab : -L < L := by linarith
  have hMem : MemLp (oddExt g) 2 (volume.restrict (Ioc (-L) L)) :=
    MemLp.of_bound (oddExt_measurable hg).aestronglyMeasurable B
      (Filter.Eventually.of_forall (oddExt_bound hB hB0))
  have hP := hasSum_sq_fourierCoeffOn hab hMem
  -- identify the coefficients
  have hcoef : ∀ i : ℤ, fourierCoeffOn hab (oddExt g) i
      = (-Complex.I / L) * ∫ x in (0 : ℝ)..L, ((Real.sin (i * Real.pi * x / L) : ℝ) : ℂ) * g x := by
    intro i
    rw [fourierCoeffOn_eq_integral]
    have := coeff_odd hL hg hB i
    simp only [fourier_coe_apply, smul_eq_mul]
    rw [this]
    have : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have h2 : ((L - -L : ℝ) : ℂ) = 2 * L := by push_cast; ring
    rw [one_div, Complex.real_smul]
    push_cast
    field_simp
    ring
  have hnorm : ∀ i : ℤ, ‖fourierCoeffOn hab (oddExt g) i‖ ^ 2
      = (‖∫ x in (0 : ℝ)..L, ((Real.sin (i * Real.pi * x / L) : ℝ) : ℂ) * g x‖ ^ 2) / L ^ 2 := by
    intro i
    rw [hcoef, norm_mul, mul_pow, norm_div, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hL]
    field_simp
  have htot : (L - -L)⁻¹ • ∫ x in (-L)..L, ‖oddExt g x‖ ^ 2 = L⁻¹ * ∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2 := by
    rw [norm_sq_odd hL hg hB, smul_eq_mul]
    have : (L - -L) = 2 * L := by ring
    rw [this]; field_simp
  rw [htot] at hP
  simp_rw [hnorm] at hP
  have hN := hP.nat_add_neg
  have h0 : (‖∫ x in (0 : ℝ)..L, ((Real.sin (((0 : ℤ) : ℝ) * Real.pi * x / L) : ℝ) : ℂ) * g x‖ ^ 2) / L ^ 2 = 0 := by
    simp
  rw [h0, add_zero] at hN
  have hmul := hN.mul_left L
  have hfun : (fun n : ℕ => (2 / L) * ‖sinCoeff L g n‖ ^ 2) = fun n : ℕ => L *
      ((‖∫ x in (0 : ℝ)..L, ((Real.sin (((n : ℤ) : ℝ) * Real.pi * x / L) : ℝ) : ℂ) * g x‖ ^ 2) / L ^ 2
      + (‖∫ x in (0 : ℝ)..L, ((Real.sin ((((-(n : ℤ)) : ℤ) : ℝ) * Real.pi * x / L) : ℝ) : ℂ) * g x‖ ^ 2) / L ^ 2) := by
    funext n
    have e1 : ∫ x in (0 : ℝ)..L, ((Real.sin ((((-(n : ℤ)) : ℤ) : ℝ) * Real.pi * x / L) : ℝ) : ℂ) * g x
        = -∫ x in (0 : ℝ)..L, ((Real.sin (((n : ℤ) : ℝ) * Real.pi * x / L) : ℝ) : ℂ) * g x := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [show ((((-(n : ℤ)) : ℤ) : ℝ) * Real.pi * x / L) = -(((n : ℤ) : ℝ) * Real.pi * x / L) by
        push_cast; ring, Real.sin_neg, Complex.ofReal_neg]
      ring
    rw [e1, norm_neg]
    simp only [sinCoeff, Int.cast_natCast]
    field_simp
    ring
  rw [hfun]
  have hr : (∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) = L * (L⁻¹ * ∫ x in (0 : ℝ)..L, ‖g x‖ ^ 2) := by
    field_simp
  rw [hr]
  exact hmul

/-! ### Real-valued form -/

/-- `∫₀ᴸ sin(nπx/L) f(x) dx` for real `f`. -/
noncomputable def rc (L : ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..L, Real.sin (n * Real.pi * x / L) * f x

theorem sinCoeff_ofReal (L : ℝ) (f : ℝ → ℝ) (n : ℕ) :
    sinCoeff L (fun x => (f x : ℂ)) n = ((rc L f n : ℝ) : ℂ) := by
  unfold sinCoeff rc
  rw [intervalIntegral.integral_ofReal.symm]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp

theorem rc_add {L : ℝ} {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) (n : ℕ) :
    rc L (fun x => f x + g x) n = rc L f n + rc L g n := by
  unfold rc
  have hs : Measurable fun x : ℝ => Real.sin (n * Real.pi * x / L) := by fun_prop
  rw [← intervalIntegral.integral_add]
  · refine intervalIntegral.integral_congr (fun x _ => ?_); simp only; ring
  · exact ii_of_bound' (B := B) (hs.mul hf) (fun x => by
      show ‖Real.sin (n * Real.pi * x / L) * f x‖ ≤ B
      rw [norm_mul]; calc _ ≤ 1 * B := mul_le_mul (by simpa using Real.abs_sin_le_one _) (by simpa using hfB x) (norm_nonneg _) zero_le_one
        _ = B := one_mul B) 0 L
  · exact ii_of_bound' (B := B) (hs.mul hg) (fun x => by
      show ‖Real.sin (n * Real.pi * x / L) * g x‖ ≤ B
      rw [norm_mul]; calc _ ≤ 1 * B := mul_le_mul (by simpa using Real.abs_sin_le_one _) (by simpa using hgB x) (norm_nonneg _) zero_le_one
        _ = B := one_mul B) 0 L

theorem sine_parseval_real {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    HasSum (fun n : ℕ => (2 / L) * (rc L f n) ^ 2) (∫ x in (0 : ℝ)..L, (f x) ^ 2) := by
  have h := sine_parseval hL (g := fun x => (f x : ℂ)) (Complex.measurable_ofReal.comp hf)
    (B := B) (fun x => by simpa using hB x)
  simp_rw [sinCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  convert h using 2

theorem rc_neg (L : ℝ) (g : ℝ → ℝ) (n : ℕ) : rc L (fun x => - g x) n = - rc L g n := by
  unfold rc
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  simp

/-- **Polarised sine Parseval**: `∫₀ᴸ f g = (2/L) Σₙ cₙ(f) cₙ(g)`. -/
theorem sine_parseval_pol {L : ℝ} (hL : 0 < L) {f g : ℝ → ℝ} (hf : Measurable f)
    (hg : Measurable g) {B : ℝ} (hfB : ∀ x, |f x| ≤ B) (hgB : ∀ x, |g x| ≤ B) :
    HasSum (fun n : ℕ => (2 / L) * (rc L f n * rc L g n)) (∫ x in (0 : ℝ)..L, f x * g x) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hfB 0)
  have hp := sine_parseval_real hL (f := fun x => f x + g x) (hf.add hg) (B := 2 * B) (fun x => by
    calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ 2 * B := by linarith [hfB x, hgB x])
  have hm := sine_parseval_real hL (f := fun x => f x + (- g x)) (hf.add hg.neg) (B := 2 * B) (fun x => by
    calc |f x + -g x| ≤ |f x| + |-g x| := abs_add_le _ _
      _ ≤ 2 * B := by rw [abs_neg]; linarith [hfB x, hgB x])
  simp_rw [rc_add hf hg hfB hgB] at hp
  have hgnB : ∀ x, |(fun x => -g x) x| ≤ B := fun x => by show |-g x| ≤ B; rw [abs_neg]; exact hgB x
  simp_rw [rc_add (g := fun x => -g x) hf hg.neg hfB hgnB, rc_neg] at hm
  have hd := (hp.sub hm).mul_left (1 / 4)
  have iint : ∀ h : ℝ → ℝ, Measurable h → (∀ x, |h x| ≤ 2 * B) →
      IntervalIntegrable (fun x => (h x) ^ 2) volume 0 L := fun h hh hb =>
    ii_of_bound' (B := (2 * B) ^ 2) (by fun_prop) (fun x => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hb x) 2) 0 L
  have i1 := iint (fun x => f x + g x) (hf.add hg) (fun x => by
    calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
      _ ≤ 2 * B := by linarith [hfB x, hgB x])
  have i2 := iint (fun x => f x + -g x) (hf.add hg.neg) (fun x => by
    calc |f x + -g x| ≤ |f x| + |-g x| := abs_add_le _ _
      _ ≤ 2 * B := by rw [abs_neg]; linarith [hfB x, hgB x])
  have hint : (1 / 4 : ℝ) * ((∫ x in (0 : ℝ)..L, (f x + g x) ^ 2) - ∫ x in (0 : ℝ)..L, (f x + -g x) ^ 2)
      = ∫ x in (0 : ℝ)..L, f x * g x := by
    rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    ring
  rw [hint] at hd
  have hfun : (fun n : ℕ => (2 / L) * (rc L f n * rc L g n)) = fun i : ℕ =>
      1 / 4 * (2 / L * (rc L f i + rc L g i) ^ 2 - 2 / L * (rc L f i + -rc L g i) ^ 2) := by
    funext n; ring
  rw [hfun]; exact hd

end GppSineBasis

#print axioms GppSineBasis.coeff_odd
#print axioms GppSineBasis.sine_parseval
#print axioms GppSineBasis.sine_parseval_pol
