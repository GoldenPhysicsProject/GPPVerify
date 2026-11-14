import GppVerify.Analysis.MellinPlancherelHalfLine

/-!
# Mellin–Plancherel on `L²`: the principal-line Mellin transform is unitary and onto

`MellinPlancherelHalfLine` proves the norm identity
`(1/2π) ∫ |𝓜f(1/2 + iτ)|² dτ = ∫_{x>0} |f(x)|² dx` for Schwartz-type `f`. This file extends it to
all of `L²((0, ∞), dx)` and proves the onto statement (completeness of the principal-series basis
in boundary dimension one). That is the analytic core of File 5 of the Pasterski–Shao formalisation
spec (GPP-bridge `MuseResearch/turbo-pss-inventory-spec-2026-11-13.md`, item (iii) and File 5).

## Main results

* `halfLineEquiv`: the substitution `x = e^{-u}` with half-density weight,
  `(T f)(u) = e^{-u/2} f(e^{-u})`, is a linear isometry equivalence
  `L²((0,∞), dx) ≃ₗᵢ L²(ℝ, du)`. Its inverse is `(S g)(x) = x^{-1/2} g(-log x)`.
* `mellinL2`: the composite `𝓕 ∘ T`, a linear isometry equivalence
  `L²((0,∞), dx) ≃ₗᵢ L²(ℝ)`. It is the principal-line Mellin transform: for `f` with `T f` a
  Schwartz function, `mellinL2 f` is (the class of) `ξ ↦ 𝓜f(1/2 + 2πiξ)` (`mellinL2_apply`).
* `mellinL2_surjective`: **completeness.** Every `L²` function on the principal line is the Mellin
  transform of an `L²` function on `(0, ∞)`.
* `mellinL2_norm`: Plancherel, `‖mellinL2 f‖ = ‖f‖`.
* `mellinInv_mellin_half`: Mellin inversion on the principal line `Re s = 1/2` (the inverse-Mellin
  expansion, PSS (4.6) in one dimension), from Mathlib's `mellinInv_mellin_eq`.
* `not_memLp_const_halfLine`: a nonzero constant on `(0, ∞)` is not in `L²`, so the zero-energy
  mode is not in the span, matching the paper's explicit clause.

Analysis only. Nothing arithmetic, no claim about the zeros. This file lives in the neutral
`Analysis/` home so physics files may import it (`scripts/check_pss_wall.py`).
-/

set_option autoImplicit false

namespace GppMellinPlancherelL2

open MeasureTheory Set Real Filter FourierTransform SchwartzMap
open scoped ENNReal

/-- Lebesgue measure on the half-line `(0, ∞)`. -/
noncomputable abbrev μHalf : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

/-! ## The substitution `x = e^{-u}` -/

theorem image_exp_neg : (fun u : ℝ => Real.exp (-u)) '' (univ : Set ℝ) = Ioi 0 := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_Ioi]
  constructor
  · rintro ⟨u, rfl⟩; exact Real.exp_pos _
  · intro hx; exact ⟨-Real.log x, by simp [Real.exp_log hx]⟩

/-- **Change of variables, `lintegral` form.** For every `G : ℝ → ℝ≥0∞`,
`∫⁻_{x>0} G x dx = ∫⁻ e^{-u} G(e^{-u}) du`. -/
theorem lintegral_halfLine (G : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioi (0 : ℝ), G x = ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-u)) * G (Real.exp (-u)) := by
  have hderiv : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) univ u := by
    intro u _
    exact ((hasDerivAt_neg u).exp.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ h
    simpa using h
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ hderiv hinj G
  rw [image_exp_neg] at h
  rw [h, Measure.restrict_univ]
  refine lintegral_congr fun u => ?_
  rw [abs_neg, abs_of_pos (Real.exp_pos _)]

/-- `u ↦ e^{-u}` sends `volume` to a measure absolutely continuous with respect to `μHalf`. -/
theorem quasiMeasurePreserving_exp_neg :
    Measure.QuasiMeasurePreserving (fun u : ℝ => Real.exp (-u)) volume μHalf := by
  refine ⟨by fun_prop, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [Measure.map_apply (by fun_prop) hA]
  have h := lintegral_halfLine (A.indicator fun x => ENNReal.ofReal x⁻¹)
  have hL : ∫⁻ x in Ioi (0 : ℝ), A.indicator (fun x => ENNReal.ofReal x⁻¹) x = 0 := by
    rw [lintegral_indicator hA]
    have : (volume.restrict (Ioi (0 : ℝ))).restrict A = 0 := by
      rw [Measure.restrict_eq_zero]; exact hA0
    rw [Measure.restrict_restrict hA] at this ⊢
    rw [this, lintegral_zero_measure]
  rw [hL] at h
  have hR : ∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (-u)) *
      A.indicator (fun x => ENNReal.ofReal x⁻¹) (Real.exp (-u)) =
      volume ((fun u : ℝ => Real.exp (-u)) ⁻¹' A) := by
    rw [← lintegral_indicator_one (measurableSet_preimage (by fun_prop) hA)]
    refine lintegral_congr fun u => ?_
    by_cases hu : Real.exp (-u) ∈ A
    · have hu' : u ∈ (fun u : ℝ => Real.exp (-u)) ⁻¹' A := hu
      rw [indicator_of_mem hu, indicator_of_mem hu', ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, Pi.one_apply]
    · have hu' : u ∉ (fun u : ℝ => Real.exp (-u)) ⁻¹' A := hu
      rw [indicator_of_notMem hu, indicator_of_notMem hu', mul_zero]
  rw [hR] at h
  exact h.symm

/-- `x ↦ -log x` sends `μHalf` to a measure absolutely continuous with respect to `volume`. -/
theorem quasiMeasurePreserving_neg_log :
    Measure.QuasiMeasurePreserving (fun x : ℝ => -Real.log x) μHalf volume := by
  refine ⟨by fun_prop, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun B hB hB0 => ?_
  rw [Measure.map_apply (by fun_prop) hB]
  have hP : MeasurableSet ((fun x : ℝ => -Real.log x) ⁻¹' B) := measurableSet_preimage (by fun_prop) hB
  have h := lintegral_halfLine (((fun x : ℝ => -Real.log x) ⁻¹' B).indicator 1)
  rw [lintegral_indicator_one hP] at h
  rw [h]
  have hR : ∀ u : ℝ, ENNReal.ofReal (Real.exp (-u)) *
      ((fun x : ℝ => -Real.log x) ⁻¹' B).indicator 1 (Real.exp (-u)) =
      B.indicator (fun u => ENNReal.ofReal (Real.exp (-u))) u := by
    intro u
    have hl : -Real.log (Real.exp (-u)) = u := by rw [Real.log_exp, neg_neg]
    by_cases hu : u ∈ B
    · have hu' : Real.exp (-u) ∈ (fun x : ℝ => -Real.log x) ⁻¹' B := by
        show -Real.log (Real.exp (-u)) ∈ B; rw [hl]; exact hu
      rw [indicator_of_mem hu', indicator_of_mem hu, Pi.one_apply, mul_one]
    · have hu' : Real.exp (-u) ∉ (fun x : ℝ => -Real.log x) ⁻¹' B := by
        show -Real.log (Real.exp (-u)) ∉ B; rw [hl]; exact hu
      rw [indicator_of_notMem hu', indicator_of_notMem hu, mul_zero]
  simp_rw [hR]
  rw [lintegral_indicator hB, Measure.restrict_eq_zero.mpr hB0, lintegral_zero_measure]

/-! ## The half-density substitution on functions -/

/-- `(T f)(u) = e^{-u/2} f(e^{-u})`. -/
noncomputable def T (f : ℝ → ℂ) (u : ℝ) : ℂ := (Real.exp (-u / 2) : ℂ) * f (Real.exp (-u))

/-- `(S g)(x) = x^{-1/2} g(-log x)`, the inverse substitution. -/
noncomputable def S (g : ℝ → ℂ) (x : ℝ) : ℂ := ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * g (-Real.log x)

theorem T_add (f g : ℝ → ℂ) : T (f + g) = T f + T g := by
  funext u; simp [T, mul_add]

theorem T_smul (c : ℂ) (f : ℝ → ℂ) : T (c • f) = c • T f := by
  funext u; simp [T]; ring

theorem S_add (f g : ℝ → ℂ) : S (f + g) = S f + S g := by
  funext x; simp [S, mul_add]

theorem S_smul (c : ℂ) (f : ℝ → ℂ) : S (c • f) = c • S f := by
  funext x; simp [S]; ring

theorem T_S (g : ℝ → ℂ) : T (S g) = g := by
  funext u
  simp only [T, S]
  rw [Real.log_exp, neg_neg, ← mul_assoc, ← Complex.ofReal_mul,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_add]
  have : -u / 2 + -u * -(1 / 2 : ℝ) = 0 := by ring
  rw [this, Real.exp_zero, Complex.ofReal_one, one_mul]

theorem S_T_of_pos (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) : S (T f) x = f x := by
  simp only [T, S]
  rw [neg_neg, Real.exp_log hx, ← mul_assoc, ← Complex.ofReal_mul,
    Real.rpow_def_of_pos hx]
  have : Real.exp (Real.log x * -(1 / 2 : ℝ)) * Real.exp (Real.log x / 2) = 1 := by
    rw [← Real.exp_add]
    have : Real.log x * -(1 / 2 : ℝ) + Real.log x / 2 = 0 := by ring
    rw [this, Real.exp_zero]
  rw [this, Complex.ofReal_one, one_mul]

theorem enorm_ofReal_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hr]

theorem enorm_sq_T (f : ℝ → ℂ) (u : ℝ) :
    ‖T f u‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Real.exp (-u)) * ‖f (Real.exp (-u))‖ₑ ^ (2 : ℝ) := by
  simp only [T, enorm_mul, ENNReal.rpow_two, mul_pow]
  congr 1
  rw [enorm_ofReal_of_nonneg (Real.exp_pos _).le, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← Real.exp_nat_mul]
  congr 2
  push_cast; ring

theorem enorm_sq_S (g : ℝ → ℂ) (u : ℝ) :
    ENNReal.ofReal (Real.exp (-u)) * ‖S g (Real.exp (-u))‖ₑ ^ (2 : ℝ) = ‖g u‖ₑ ^ (2 : ℝ) := by
  simp only [S, enorm_mul, ENNReal.rpow_two, mul_pow]
  rw [Real.log_exp, neg_neg, ← mul_assoc]
  have hpos : 0 < Real.exp (-u) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (Real.exp_pos _) _
  rw [enorm_ofReal_of_nonneg hpos.le, ← ENNReal.ofReal_pow hpos.le,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  have : Real.exp (-u) * (Real.exp (-u) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
    have : -u + ((2 : ℕ) : ℝ) * (-u * -(1 / 2 : ℝ)) = 0 := by push_cast; ring
    rw [this, Real.exp_zero]
  rw [this, ENNReal.ofReal_one, one_mul]

theorem lintegral_T (f : ℝ → ℂ) :
    ∫⁻ u, ‖T f u‖ₑ ^ (2 : ℝ) = ∫⁻ x in Ioi (0 : ℝ), ‖f x‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_halfLine]
  exact lintegral_congr fun u => enorm_sq_T f u

theorem lintegral_S (g : ℝ → ℂ) :
    ∫⁻ x in Ioi (0 : ℝ), ‖S g x‖ₑ ^ (2 : ℝ) = ∫⁻ u, ‖g u‖ₑ ^ (2 : ℝ) := by
  rw [lintegral_halfLine]
  exact lintegral_congr fun u => enorm_sq_S g u

theorem eLpNorm_T (f : ℝ → ℂ) : eLpNorm (T f) 2 volume = eLpNorm f 2 μHalf := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_T]

theorem eLpNorm_S (g : ℝ → ℂ) : eLpNorm (S g) 2 μHalf = eLpNorm g 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_S]

theorem aestronglyMeasurable_T {f : ℝ → ℂ} (hf : AEStronglyMeasurable f μHalf) :
    AEStronglyMeasurable (T f) volume := by
  have h := hf.comp_quasiMeasurePreserving quasiMeasurePreserving_exp_neg
  exact (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun u : ℝ =>
    Real.exp (-u / 2))).aestronglyMeasurable.mul h

theorem aestronglyMeasurable_S {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (S g) μHalf := by
  have h := hg.comp_quasiMeasurePreserving quasiMeasurePreserving_neg_log
  have hm : Measurable fun x : ℝ => ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by fun_prop
  exact hm.aestronglyMeasurable.mul h

theorem T_ae_congr {f f' : ℝ → ℂ} (h : f =ᵐ[μHalf] f') : T f =ᵐ[volume] T f' := by
  have h' := quasiMeasurePreserving_exp_neg.ae_eq h
  filter_upwards [h'] with u hu
  simp only [T, Function.comp_apply] at hu ⊢
  rw [hu]

theorem S_ae_congr {g g' : ℝ → ℂ} (h : g =ᵐ[volume] g') : S g =ᵐ[μHalf] S g' := by
  have h' := quasiMeasurePreserving_neg_log.ae_eq h
  filter_upwards [h'] with x hx
  simp only [S, Function.comp_apply] at hx ⊢
  rw [hx]

/-! ## The `L²` unitary -/

theorem memLp_T (f : Lp ℂ 2 μHalf) : MemLp (T f) 2 volume :=
  ⟨aestronglyMeasurable_T (Lp.aestronglyMeasurable f), by rw [eLpNorm_T]; exact Lp.eLpNorm_lt_top f⟩

theorem memLp_S (g : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (S g) 2 μHalf :=
  ⟨aestronglyMeasurable_S (Lp.aestronglyMeasurable g), by rw [eLpNorm_S]; exact Lp.eLpNorm_lt_top g⟩

/-- `T` as a linear isometry `L²((0,∞), dx) → L²(ℝ, du)`. -/
noncomputable def Tli : Lp ℂ 2 μHalf →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (memLp_T f).toLp (T f)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have h := T_ae_congr (Lp.coeFn_add f g)
    rwa [T_add] at h
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have h := T_ae_congr (Lp.coeFn_smul c f)
    rwa [T_smul] at h
  norm_map' f := by
    show ‖(memLp_T f).toLp (T f)‖ = ‖f‖
    rw [Lp.norm_toLp, eLpNorm_T, Lp.norm_def]

/-- `S` as a linear isometry `L²(ℝ, du) → L²((0,∞), dx)`. -/
noncomputable def Sli : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 μHalf where
  toFun g := (memLp_S g).toLp (S g)
  map_add' f g := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ ?_
    have h := S_ae_congr (Lp.coeFn_add f g)
    rwa [S_add] at h
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ ?_
    have h := S_ae_congr (Lp.coeFn_smul c f)
    rwa [S_smul] at h
  norm_map' g := by
    show ‖(memLp_S g).toLp (S g)‖ = ‖g‖
    rw [Lp.norm_toLp, eLpNorm_S, Lp.norm_def]

theorem Tli_Sli (g : Lp ℂ 2 (volume : Measure ℝ)) : Tli (Sli g) = g := by
  have h1 : (Tli (Sli g) : ℝ → ℂ) =ᵐ[volume] T (Sli g) := MemLp.coeFn_toLp (memLp_T (Sli g))
  have h2 : (Sli g : ℝ → ℂ) =ᵐ[μHalf] S g := MemLp.coeFn_toLp (memLp_S g)
  have h3 := T_ae_congr h2
  rw [T_S] at h3
  exact Lp.ext (h1.trans h3)

theorem Sli_Tli (f : Lp ℂ 2 μHalf) : Sli (Tli f) = f := by
  have h1 : (Sli (Tli f) : ℝ → ℂ) =ᵐ[μHalf] S (Tli f) := MemLp.coeFn_toLp (memLp_S (Tli f))
  have h2 : (Tli f : ℝ → ℂ) =ᵐ[volume] T f := MemLp.coeFn_toLp (memLp_T f)
  have h3 := S_ae_congr h2
  have h4 : S (T f) =ᵐ[μHalf] f := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun x hx => S_T_of_pos f hx
  exact Lp.ext (h1.trans (h3.trans h4))

/-- **The half-density substitution is unitary.** `L²((0,∞), dx) ≃ₗᵢ L²(ℝ, du)`,
`f ↦ (u ↦ e^{-u/2} f(e^{-u}))`. -/
noncomputable def halfLineEquiv : Lp ℂ 2 μHalf ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective Tli fun g => ⟨Sli g, Tli_Sli g⟩

/-- **The principal-line Mellin transform on `L²`.** `L²((0,∞), dx) ≃ₗᵢ L²(ℝ)`, the composite of the
half-density substitution and the `L²` Fourier transform. -/
noncomputable def mellinL2 : Lp ℂ 2 μHalf ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  halfLineEquiv.trans (Lp.fourierTransformₗᵢ ℝ ℂ)

/-- **Plancherel on `L²`.** -/
theorem mellinL2_norm (f : Lp ℂ 2 μHalf) : ‖mellinL2 f‖ = ‖f‖ := mellinL2.norm_map f

/-- **Completeness.** Every `L²` function of the principal-line variable is the Mellin transform of
an `L²` function on `(0, ∞)`: the principal series spans. -/
theorem mellinL2_surjective : Function.Surjective mellinL2 := mellinL2.surjective

/-- **`mellinL2` is the Mellin transform on the principal line.** If `f ∈ L²((0,∞))` and
`u ↦ e^{-u/2} f(e^{-u})` is a Schwartz function `g`, then `mellinL2 f` is the class of
`ξ ↦ 𝓜f(1/2 + 2πiξ)`. -/
theorem mellinL2_apply {f : ℝ → ℂ} (hf : MemLp f 2 μHalf) (g : 𝓢(ℝ, ℂ))
    (hg : ∀ u, T f u = g u) :
    (mellinL2 (hf.toLp f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ : ℝ => mellin f ((1 / 2 : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * Complex.I) := by
  have hT : halfLineEquiv (hf.toLp f) = g.toLp 2 := by
    have h1 : (halfLineEquiv (hf.toLp f) : ℝ → ℂ) =ᵐ[volume] T (hf.toLp f) :=
      MemLp.coeFn_toLp (memLp_T (hf.toLp f))
    have h2 := T_ae_congr (MemLp.coeFn_toLp hf)
    have h3a : T f =ᵐ[volume] (g : ℝ → ℂ) := Filter.Eventually.of_forall hg
    have h3 : T f =ᵐ[volume] (g.toLp 2 : ℝ → ℂ) :=
      h3a.trans (SchwartzMap.coeFn_toLp g 2 volume).symm
    exact Lp.ext (h1.trans (h2.trans h3))
  have hF : mellinL2 (hf.toLp f) = (𝓕 g).toLp 2 := by
    show Lp.fourierTransformₗᵢ ℝ ℂ (halfLineEquiv (hf.toLp f)) = _
    rw [hT]
    exact SchwartzMap.toLp_fourier_eq g
  rw [hF]
  refine (SchwartzMap.coeFn_toLp (𝓕 g) 2 volume).trans (Filter.Eventually.of_forall fun ξ => ?_)
  have hfun : (fun u : ℝ => Real.exp (-((1 / 2 : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * Complex.I).re * u) •
      f (Real.exp (-u))) = (g : ℝ → ℂ) := by
    funext u
    rw [← hg u]
    simp only [T, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.real_smul]
    congr 2
    norm_num
    ring
  show (𝓕 g) ξ = mellin f ((1 / 2 : ℂ) + ((2 * π * ξ : ℝ) : ℂ) * Complex.I)
  rw [mellin_eq_fourier, hfun]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, mul_zero, mul_one]
  have harg : ((1 / 2 : ℂ).im + (2 * π * ξ + 0)) / (2 * π) = ξ := by
    have hpi : (2 * π : ℝ) ≠ 0 := by positivity
    rw [show (1 / 2 : ℂ).im = 0 by norm_num, zero_add, add_zero]
    field_simp
  rw [harg, SchwartzMap.fourier_coe]

/-! ## Inversion and the zero-energy mode -/

/-- **Mellin inversion on the principal line** `Re s = 1/2`: the inverse-Mellin expansion
(Pasterski–Shao (4.6), boundary dimension one). -/
theorem mellinInv_mellin_half (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hf : MellinConvergent f ((1 / 2 : ℝ) : ℂ))
    (hFf : Complex.VerticalIntegrable (mellin f) (1 / 2)) (hfx : ContinuousAt f x) :
    mellinInv (1 / 2) (mellin f) x = f x :=
  mellinInv_mellin_eq (1 / 2) f hx hf hFf hfx

/-- **The zero-energy mode is not spanned.** A nonzero constant on `(0, ∞)` is not in `L²`. -/
theorem not_memLp_const_halfLine {c : ℂ} (hc : c ≠ 0) : ¬ MemLp (fun _ : ℝ => c) 2 μHalf := by
  rw [memLp_const_iff_enorm enorm_ne_top two_ne_zero ENNReal.ofNat_ne_top]
  rintro (h | h)
  · exact hc (enorm_eq_zero.mp h)
  · rw [Measure.restrict_apply_univ, Real.volume_Ioi] at h
    exact lt_irrefl _ h

end GppMellinPlancherelL2
