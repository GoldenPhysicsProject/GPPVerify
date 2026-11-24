import GppVerify.RiemannHypothesis.OddFaceSineAtoms
import Mathlib.Analysis.Fourier.AddCircle

/-!
# OddFace(0.5): completeness of the sine modes (Parseval on `[0, ℓ]`)

The Parseval half of Heart's Round 10 identity `CCᵀ = Gram(k) − HHᵀ` (GPP-bridge PR #11, comment
6890476616; Turbo's audit 6890691322): once the coupling rows are `C̃_{a,j} = ⟨k_a, φ_j⟩`, the identity
needs `Σ_j ⟨k_a, φ_j⟩⟨k_b, φ_j⟩ = ⟨k_a, k_b⟩` for the continuous `k_a`. `#604` supplied the Green step
(`green_phi`) and `#603` the finite Parseval; this file closes the infinite one.

**`sine_parseval`.** For `ℓ > 0` and continuous `f : ℝ → ℝ`,

  `Σ_{j ≥ 0} (∫₀^ℓ f φ_j)² = ∫₀^ℓ f²`,    `φ_j(x) = √(2/ℓ) sin(jπx/ℓ)`.

(`φ₀ = 0`, so the `j = 0` term is `0`.) **`sine_parseval_bilinear`** is the polarised form
`Σ_j ⟨f, φ_j⟩⟨g, φ_j⟩ = ⟨f, g⟩`, which is the form the coupling identity consumes.

**Proof.** The odd extension `F` of `f` to `[−ℓ, ℓ]` is bounded and measurable, so it is `L²` there.
Its complex Fourier coefficients on `[−ℓ, ℓ]` are `c_n = (−i/ℓ) ∫₀^ℓ f(x) sin(nπx/ℓ) dx`: the cosine
part of `e^{-iπnx/ℓ}` pairs an even function with the odd `F` and integrates to `0`, the sine part
doubles. So `|c_n|² = ⟨f, φ_{|n|}⟩²/(2ℓ)`. Mathlib's `hasSum_sq_fourierCoeffOn` gives
`Σ_{n∈ℤ} |c_n|² = (2ℓ)⁻¹ ∫_{-ℓ}^{ℓ} F² = ℓ⁻¹ ∫₀^ℓ f²`; folding `n` and `−n` with
`HasSum.nat_add_neg` gives the claim.

**Scope.** `f` is continuous on `ℝ` (a function continuous on `[0, ℓ]` extends by clamping).
 Nothing here depends on the arch form, the explicit
formula, or any zero data. OddFace(0.5) stays NUMERICAL; proof-grade OPEN on (H-A), (H-ρ). RH OPEN.
No `sorry`, no axioms.
-/

namespace GppOddFaceSineParseval

open Real MeasureTheory Set intervalIntegral GppOddFaceAtoms

/-! ### The odd extension -/

/-- The odd extension of `f` from `(0, ∞)` to `ℝ`. -/
noncomputable def oddExt (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 < x then f x else if x < 0 then -f (-x) else 0

theorem oddExt_of_pos {f : ℝ → ℝ} {x : ℝ} (h : 0 < x) : oddExt f x = f x := by
  simp [oddExt, h]

theorem oddExt_of_neg {f : ℝ → ℝ} {x : ℝ} (h : x < 0) : oddExt f x = -f (-x) := by
  simp [oddExt, not_lt.2 h.le, h]

theorem oddExt_neg (f : ℝ → ℝ) (x : ℝ) : oddExt f (-x) = -oddExt f x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [oddExt_of_pos (neg_pos.2 h), oddExt_of_neg h]; simp
  · subst h; simp [oddExt]
  · rw [oddExt_of_neg (neg_lt_zero.2 h), oddExt_of_pos h]; simp

theorem measurable_oddExt {f : ℝ → ℝ} (hf : Continuous f) : Measurable (oddExt f) := by
  unfold oddExt
  exact Measurable.ite measurableSet_Ioi hf.measurable
    (Measurable.ite measurableSet_Iio (hf.measurable.comp measurable_neg).neg measurable_const)

theorem oddExt_bound {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-ℓ) ℓ, |oddExt f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := ℓ)).exists_bound_of_continuousOn
    hf.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, hℓ.le⟩)
  refine ⟨C, hC0, fun x hx => ?_⟩
  rcases lt_trichotomy x 0 with h | h | h
  · rw [oddExt_of_neg h, abs_neg]
    simpa using hC (-x) ⟨by linarith, by linarith [hx.1]⟩
  · subst h; simpa [oddExt] using hC0
  · rw [oddExt_of_pos h]
    simpa using hC x ⟨h.le, hx.2⟩

/-! ### Integrals over `[-a, a]` of odd and even functions -/

theorem integral_odd_eq_zero {g : ℝ → ℝ} (hg : ∀ x, g (-x) = -g x) (a : ℝ) :
    ∫ x in (-a)..a, g x = 0 := by
  have h := intervalIntegral.integral_comp_neg (a := -a) (b := a) (fun x => g x)
  rw [neg_neg] at h
  simp_rw [hg, intervalIntegral.integral_neg] at h
  linarith

theorem integral_even_eq_two_mul {g : ℝ → ℝ} (hg : ∀ x, g (-x) = g x) {a : ℝ} (ha : 0 ≤ a)
    (hint : IntervalIntegrable g volume (-a) a) :
    ∫ x in (-a)..a, g x = 2 * ∫ x in (0 : ℝ)..a, g x := by
  have h1 : IntervalIntegrable g volume (-a) 0 :=
    hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                      exact Icc_subset_Icc le_rfl ha)
  have h2 : IntervalIntegrable g volume 0 a :=
    hint.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
                      exact Icc_subset_Icc (by linarith) le_rfl)
  have hneg := intervalIntegral.integral_comp_neg (a := 0) (b := a) (fun x => g x)
  rw [neg_zero] at hneg
  simp_rw [hg] at hneg
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, ← hneg]
  ring

theorem intervalIntegrable_of_bdd {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hg : Measurable g)
    (C : ℝ) (hC : ∀ x ∈ Icc a b, |g x| ≤ C) : IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  simpa using hC x (Ioc_subset_Icc_self hx)

/-! ### The `cos` and `sin` moments of the odd extension -/

theorem measurable_trig_oddExt {f : ℝ → ℝ} (hf : Continuous f) {w : ℝ → ℝ}
    (hw : Measurable w) : Measurable fun x => w x * oddExt f x :=
  hw.mul (measurable_oddExt hf)

theorem intervalIntegrable_trig_oddExt {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {w : ℝ → ℝ} (hw : Measurable w) (hw1 : ∀ x, |w x| ≤ 1) :
    IntervalIntegrable (fun x => w x * oddExt f x) volume (-ℓ) ℓ := by
  obtain ⟨C, hC0, hC⟩ := oddExt_bound hf hℓ
  refine intervalIntegrable_of_bdd (by linarith) (measurable_trig_oddExt hf hw) C fun x hx => ?_
  rw [abs_mul]
  calc |w x| * |oddExt f x| ≤ 1 * C := mul_le_mul (hw1 x) (hC x hx) (abs_nonneg _) zero_le_one
    _ = C := one_mul C

theorem integral_cos_oddExt {f : ℝ → ℝ} (ℓ s : ℝ) :
    ∫ x in (-ℓ)..ℓ, cos (s * x) * oddExt f x = 0 :=
  integral_odd_eq_zero (fun x => by rw [oddExt_neg]; simp [mul_neg, Real.cos_neg]) ℓ

theorem integral_sin_oddExt {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) (s : ℝ) :
    ∫ x in (-ℓ)..ℓ, sin (s * x) * oddExt f x = 2 * ∫ x in (0 : ℝ)..ℓ, f x * sin (s * x) := by
  have hint := intervalIntegrable_trig_oddExt hf hℓ (w := fun x => sin (s * x))
    (by fun_prop) (fun x => abs_sin_le_one _)
  rw [integral_even_eq_two_mul (fun x => by rw [oddExt_neg]; simp [mul_neg, Real.sin_neg]) hℓ.le
    hint]
  congr 1
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hℓ.le] at hx
  rcases hx.1.eq_or_lt with h | h
  · subst h; simp
  · simp only [oddExt_of_pos h]; ring

/-! ### The Fourier coefficients of the odd extension on `[-ℓ, ℓ]` -/

theorem fourier_neg_coe {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) (x : ℝ) :
    fourier (-n) (x : AddCircle (ℓ - -ℓ))
      = ((cos (π * n / ℓ * x) : ℝ) : ℂ) - Complex.I * ((sin (π * n / ℓ * x) : ℝ) : ℂ) := by
  rw [fourier_coe_apply]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have h : 2 * (π : ℂ) * Complex.I * ((-n : ℤ) : ℂ) * (x : ℂ) / ((ℓ - -ℓ : ℝ) : ℂ)
      = ((-(π * n / ℓ * x) : ℝ) : ℂ) * Complex.I := by
    push_cast; field_simp; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
    Real.sin_neg]
  push_cast; ring

/-- **The coefficients of the odd extension are the sine coefficients of `f`:**
`c_n = (−i/ℓ) ∫₀^ℓ f(x) sin(nπx/ℓ) dx`. -/
theorem fourierCoeffOn_oddExt {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) :
    fourierCoeffOn (show -ℓ < ℓ by linarith) (fun x => ((oddExt f x : ℝ) : ℂ)) n
      = (-Complex.I / (ℓ : ℂ)) * ((∫ x in (0 : ℝ)..ℓ, f x * sin (π * n / ℓ * x) : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  set s : ℝ := π * n / ℓ with hs
  have hcos := intervalIntegrable_trig_oddExt hf hℓ (w := fun x => cos (s * x))
    (by fun_prop) (fun x => abs_cos_le_one _)
  have hsin := intervalIntegrable_trig_oddExt hf hℓ (w := fun x => sin (s * x))
    (by fun_prop) (fun x => abs_sin_le_one _)
  have hcosC : IntervalIntegrable (fun x => ((cos (s * x) * oddExt f x : ℝ) : ℂ)) volume (-ℓ) ℓ :=
    ⟨hcos.1.ofReal, hcos.2.ofReal⟩
  have hsinC : IntervalIntegrable (fun x => ((sin (s * x) * oddExt f x : ℝ) : ℂ)) volume (-ℓ) ℓ :=
    ⟨hsin.1.ofReal, hsin.2.ofReal⟩
  have hintegrand : ∀ x : ℝ, fourier (-n) (x : AddCircle (ℓ - -ℓ)) • ((oddExt f x : ℝ) : ℂ)
      = ((cos (s * x) * oddExt f x : ℝ) : ℂ) - Complex.I * ((sin (s * x) * oddExt f x : ℝ) : ℂ) := by
    intro x
    rw [fourier_neg_coe hℓ, smul_eq_mul, hs]
    push_cast; ring
  simp_rw [hintegrand]
  rw [intervalIntegral.integral_sub hcosC (hsinC.const_mul Complex.I),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, integral_cos_oddExt, integral_sin_oddExt hf hℓ, Complex.real_smul]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  field_simp
  ring

/-! ### Parseval for the sine modes -/

/-- The sine moment of `f` at integer frequency `n`. -/
noncomputable def sineMoment (f : ℝ → ℝ) (ℓ : ℝ) (n : ℤ) : ℝ :=
  ∫ x in (0 : ℝ)..ℓ, f x * sin (π * n / ℓ * x)

theorem norm_sq_coeff {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℤ) :
    ‖fourierCoeffOn (show -ℓ < ℓ by linarith) (fun x => ((oddExt f x : ℝ) : ℂ)) n‖ ^ 2
      = sineMoment f ℓ n ^ 2 / ℓ ^ 2 := by
  rw [fourierCoeffOn_oddExt hf hℓ, norm_mul, norm_div, norm_neg, Complex.norm_I,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hℓ]
  unfold sineMoment
  rw [mul_pow, div_pow, sq_abs]
  field_simp

theorem memLp_oddExt {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MemLp (fun x => ((oddExt f x : ℝ) : ℂ)) 2 (volume.restrict (Ioc (-ℓ) ℓ)) := by
  obtain ⟨C, hC0, hC⟩ := oddExt_bound hf hℓ
  refine MemLp.of_bound (C := C) ?_ ?_
  · exact (Complex.measurable_ofReal.comp (measurable_oddExt hf)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hC x (Ioc_subset_Icc_self hx)

theorem integral_sq_oddExt {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ x in (-ℓ)..ℓ, ‖((oddExt f x : ℝ) : ℂ)‖ ^ 2 = 2 * ∫ x in (0 : ℝ)..ℓ, f x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := oddExt_bound hf hℓ
  have hn : ∀ x, ‖((oddExt f x : ℝ) : ℂ)‖ ^ 2 = oddExt f x ^ 2 := fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [hn]
  have hint : IntervalIntegrable (fun x => oddExt f x ^ 2) volume (-ℓ) ℓ := by
    refine intervalIntegrable_of_bdd (by linarith) ((measurable_oddExt hf).pow_const 2) (C ^ 2)
      fun x hx => ?_
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hC x hx) 2
  rw [integral_even_eq_two_mul (fun x => by rw [oddExt_neg]; ring) hℓ.le hint]
  congr 1
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  rw [uIoc_of_le hℓ.le] at hx
  simp only [oddExt_of_pos hx.1]

theorem sineMoment_neg (f : ℝ → ℝ) (ℓ : ℝ) (n : ℤ) :
    sineMoment f ℓ (-n) = -sineMoment f ℓ n := by
  unfold sineMoment
  rw [← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp [mul_neg, neg_mul, Real.sin_neg, neg_div]

theorem sineMoment_zero (f : ℝ → ℝ) (ℓ : ℝ) : sineMoment f ℓ 0 = 0 := by
  simp [sineMoment]

theorem inner_phi_eq {f : ℝ → ℝ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : ℕ) :
    (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) ^ 2 = 2 / ℓ * sineMoment f ℓ j ^ 2 := by
  have h : ∀ x, f x * phi ℓ j x = √(2 / ℓ) * (f x * sin (π * (j : ℤ) / ℓ * x)) := fun x => by
    unfold phi om; push_cast; ring_nf
  simp_rw [h]
  rw [intervalIntegral.integral_const_mul, mul_pow, Real.sq_sqrt (by positivity)]
  rfl

/-- **Parseval for the sine modes (completeness).** For continuous `f` and `ℓ > 0`,
`Σ_j (∫₀^ℓ f φ_j)² = ∫₀^ℓ f²`. -/
theorem sine_parseval {f : ℝ → ℝ} (hf : Continuous f) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    HasSum (fun j : ℕ => (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) ^ 2) (∫ x in (0 : ℝ)..ℓ, f x ^ 2) := by
  have H := hasSum_sq_fourierCoeffOn (show -ℓ < ℓ by linarith) (memLp_oddExt hf hℓ)
  rw [integral_sq_oddExt hf hℓ] at H
  simp_rw [norm_sq_coeff hf hℓ] at H
  have H2 := H.nat_add_neg
  have H3 := H2.mul_left ℓ
  rw [sineMoment_zero] at H3
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have h2ℓ : ℓ - -ℓ = 2 * ℓ := by ring
  have hval : ℓ * ((ℓ - -ℓ)⁻¹ • (2 * ∫ x in (0 : ℝ)..ℓ, f x ^ 2) + 0 ^ 2 / ℓ ^ 2)
      = ∫ x in (0 : ℝ)..ℓ, f x ^ 2 := by
    rw [smul_eq_mul, h2ℓ]; field_simp; ring
  have hfun : ∀ j : ℕ, (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) ^ 2
      = ℓ * (sineMoment f ℓ j ^ 2 / ℓ ^ 2 + sineMoment f ℓ (-(j : ℤ)) ^ 2 / ℓ ^ 2) := by
    intro j
    rw [inner_phi_eq hℓ j, sineMoment_neg, neg_sq]
    field_simp
    ring
  rw [hval] at H3
  have e : (fun j : ℕ => (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) ^ 2)
      = fun j : ℕ => ℓ * (sineMoment f ℓ j ^ 2 / ℓ ^ 2 + sineMoment f ℓ (-(j : ℤ)) ^ 2 / ℓ ^ 2) :=
    funext hfun
  rw [e]
  exact H3

/-- **Polarised Parseval.** `Σ_j ⟨f, φ_j⟩⟨g, φ_j⟩ = ⟨f, g⟩` on `[0, ℓ]` for continuous `f, g`. This is
the form in which Heart's `CCᵀ = Gram(k) − HHᵀ` consumes completeness. -/
theorem sine_parseval_bilinear {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) {ℓ : ℝ}
    (hℓ : 0 < ℓ) :
    HasSum (fun j : ℕ => (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) * (∫ x in (0 : ℝ)..ℓ, g x * phi ℓ j x))
      (∫ x in (0 : ℝ)..ℓ, f x * g x) := by
  have hφ : ∀ j, Continuous (phi ℓ j) := fun j => by unfold phi; fun_prop
  have hp := sine_parseval (hf.add hg) hℓ
  have hm := sine_parseval (hf.sub hg) hℓ
  have hd4 := (hp.sub hm).mul_left (1 / 4)
  have hfun : ∀ j : ℕ,
      (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) * (∫ x in (0 : ℝ)..ℓ, g x * phi ℓ j x)
        = 1 / 4 * ((∫ x in (0 : ℝ)..ℓ, (f + g) x * phi ℓ j x) ^ 2
            - (∫ x in (0 : ℝ)..ℓ, (f - g) x * phi ℓ j x) ^ 2) := by
    intro j
    have hfi : IntervalIntegrable (fun x => f x * phi ℓ j x) volume 0 ℓ :=
      (hf.mul (hφ j)).intervalIntegrable _ _
    have hgi : IntervalIntegrable (fun x => g x * phi ℓ j x) volume 0 ℓ :=
      (hg.mul (hφ j)).intervalIntegrable _ _
    have e1 : ∫ x in (0 : ℝ)..ℓ, (f + g) x * phi ℓ j x
        = (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) + ∫ x in (0 : ℝ)..ℓ, g x * phi ℓ j x := by
      simp only [Pi.add_apply, add_mul]
      exact intervalIntegral.integral_add hfi hgi
    have e2 : ∫ x in (0 : ℝ)..ℓ, (f - g) x * phi ℓ j x
        = (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) - ∫ x in (0 : ℝ)..ℓ, g x * phi ℓ j x := by
      simp only [Pi.sub_apply, sub_mul]
      exact intervalIntegral.integral_sub hfi hgi
    rw [e1, e2]; ring
  have hval : 1 / 4 * ((∫ x in (0 : ℝ)..ℓ, (f + g) x ^ 2) - ∫ x in (0 : ℝ)..ℓ, (f - g) x ^ 2)
      = ∫ x in (0 : ℝ)..ℓ, f x * g x := by
    have hi1 : IntervalIntegrable (fun x => (f + g) x ^ 2) volume 0 ℓ :=
      (Continuous.pow (hf.add hg) 2).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun x => (f - g) x ^ 2) volume 0 ℓ :=
      (Continuous.pow (hf.sub hg) 2).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1 hi2]
    have : ∀ x, (f + g) x ^ 2 - (f - g) x ^ 2 = 4 * (f x * g x) := fun x => by
      simp only [Pi.add_apply, Pi.sub_apply]; ring
    simp_rw [this]
    rw [intervalIntegral.integral_const_mul]
    ring
  rw [hval] at hd4
  have e : (fun j : ℕ => (∫ x in (0 : ℝ)..ℓ, f x * phi ℓ j x) * (∫ x in (0 : ℝ)..ℓ, g x * phi ℓ j x))
      = fun j : ℕ => 1 / 4 * ((∫ x in (0 : ℝ)..ℓ, (f + g) x * phi ℓ j x) ^ 2
          - (∫ x in (0 : ℝ)..ℓ, (f - g) x * phi ℓ j x) ^ 2) := funext hfun
  rw [e]
  exact hd4

end GppOddFaceSineParseval

#print axioms GppOddFaceSineParseval.sine_parseval
#print axioms GppOddFaceSineParseval.sine_parseval_bilinear
