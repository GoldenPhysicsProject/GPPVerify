import GppVerify.CelestialHolography.ConformalShadowPrincipalSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Half-density dilations in every boundary dimension

Source: Codex, GPP-bridge PR #11 comment 6392669042 ("derivation to exploit"). It anchors the
equator thread (`GppEquatorSU2`, `GppEquatorThermal`) in the existing holographic-chain
material: `GppConformalShadowPrincipalSeries` (the shadow `Δ ↦ d − Δ` equals conjugation exactly
on `Re Δ = d/2`), `GppPrincipalSeriesDilationBridge` (the `d = 1, 2` dilation characters), and
`GppHolographicChain`. Daniel Toupin / Golden Physics Project, with AI assistance from Codex
(statement) and Claude Code (formalization).

Let `E` be a real finite-dimensional inner-product space of dimension `d`, for example
`ℝ^d`, with an additive Haar measure `μ`. Put `(U_a f)(x) = a^{d/2} f(a x)`.

* `integral_normSq_dilate`: `∫ |U_a f|² dμ = ∫ |f|² dμ` for every `a > 0` and every `f`.
  The Jacobian `a^d` is exactly cancelled by the half-density factor `a^{d/2}` squared.
* `dilate_homogeneous`: the homogeneous mode `|x|^{−Δ}` is an eigenvector,
  `U_a |x|^{−Δ} = λ_a(Δ) |x|^{−Δ}` with `λ_a(Δ) = a^{d/2} a^{−Δ}`.
* `norm_eigen`: `|λ_a(Δ)| = a^{d/2 − Re Δ}`.
* `norm_eigen_eq_one_iff`: for `a ≠ 1`, `|λ_a(Δ)| = 1 ↔ Re Δ = d/2`.
* `norm_eigen_eq_one_iff_shadow`: for `a ≠ 1`, `|λ_a(Δ)| = 1` if and only if the conformal
  shadow `d − Δ` equals `conj Δ`. This links the unitary dilation axis to the existing
  shadow/conjugation criterion, uniformly in `d`.

**Scope.** `|x|^{−Δ}` is a formal eigenfunction and is not in `L²`; the principal-series
Hilbert-space completion is not constructed here. In particular, the axis being
"one-dimensional" (one real parameter `ν` in `Δ = d/2 + iν`) does not reduce the boundary to one
spatial dimension. No intertwiner from the equatorial `S¹` (`d = 1`) to the horizon `S²`
(`d = 2`) is constructed. No claim about RH, BSD or black-hole entropy.
-/

set_option autoImplicit false

open MeasureTheory Complex

namespace GppHalfDensityDilation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The boundary dimension `d = dim E`. -/
noncomputable abbrev dim (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : ℝ :=
  (Module.finrank ℝ E : ℝ)

/-- The half-density dilation `(U_a f)(x) = a^{d/2} f(a x)`. -/
noncomputable def dilate (a : ℝ) (f : E → ℂ) (x : E) : ℂ :=
  ((a ^ (dim E / 2) : ℝ) : ℂ) * f (a • x)

/-- **Unitarity.** `∫ |U_a f|² dμ = ∫ |f|² dμ`. -/
theorem integral_normSq_dilate [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {a : ℝ} (ha : 0 < a)
    (f : E → ℂ) : ∫ x, ‖dilate a f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have hsq : (a ^ (dim E / 2)) ^ 2 = a ^ Module.finrank ℝ E := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_natCast]
    congr 1; push_cast; ring
  have hpt : ∀ x, ‖dilate a f x‖ ^ 2 = a ^ Module.finrank ℝ E * ‖f (a • x)‖ ^ 2 := by
    intro x
    rw [dilate, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ha _), hsq]
  simp_rw [hpt]
  rw [integral_const_mul, Measure.integral_comp_smul μ (fun y => ‖f y‖ ^ 2) a, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos ha _)), ← mul_assoc, mul_inv_cancel₀ (pow_pos ha _).ne', one_mul]

/-- The dilation eigenvalue `λ_a(Δ) = a^{d/2} a^{−Δ}` of the homogeneous mode. -/
noncomputable def eigen (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ)
    (Δ : ℂ) : ℂ :=
  ((a ^ (dim E / 2) : ℝ) : ℂ) * (a : ℂ) ^ (-Δ)

/-- **Homogeneous modes are eigenvectors.** `U_a |x|^{−Δ} = λ_a(Δ) |x|^{−Δ}`. -/
theorem dilate_homogeneous {a : ℝ} (ha : 0 < a) (Δ : ℂ) (x : E) :
    dilate a (fun y => ((‖y‖ : ℝ) : ℂ) ^ (-Δ)) x = eigen E a Δ * ((‖x‖ : ℝ) : ℂ) ^ (-Δ) := by
  rw [dilate, eigen, norm_smul, Real.norm_eq_abs, abs_of_pos ha, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg ha.le (norm_nonneg x)]
  ring

/-- `|λ_a(Δ)| = a^{d/2 − Re Δ}`. -/
theorem norm_eigen {a : ℝ} (ha : 0 < a) (Δ : ℂ) :
    ‖eigen E a Δ‖ = a ^ (dim E / 2 - Δ.re) := by
  rw [eigen, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ha _),
    Complex.norm_cpow_eq_rpow_re_of_pos ha, Complex.neg_re, sub_eq_add_neg,
    Real.rpow_add ha]

/-- **The unitary axis.** For `a ≠ 1`, `|λ_a(Δ)| = 1 ↔ Re Δ = d/2`. -/
theorem norm_eigen_eq_one_iff {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (Δ : ℂ) :
    ‖eigen E a Δ‖ = 1 ↔ Δ.re = dim E / 2 := by
  rw [norm_eigen ha]
  have hlog : Real.log a ≠ 0 := by
    intro h
    rcases Real.log_eq_zero.mp h with h | h | h <;> [linarith; exact ha1 h; linarith]
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_rpow ha, Real.log_one, mul_eq_zero] at this
    rcases this with h' | h'
    · linarith
    · exact absurd h' hlog
  · intro h
    rw [h, sub_self, Real.rpow_zero]

/-- **Bridge to the shadow criterion.** For `a ≠ 1`, the half-density dilation acts unitarily on
the mode `|x|^{−Δ}` exactly when the conformal shadow `d − Δ` equals `conj Δ`. -/
theorem norm_eigen_eq_one_iff_shadow {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (Δ : ℂ) :
    ‖eigen E a Δ‖ = 1 ↔
      GppConformalShadowPrincipalSeries.conformalShadow (dim E) Δ = (starRingEnd ℂ) Δ := by
  rw [norm_eigen_eq_one_iff ha ha1, GppConformalShadowPrincipalSeries.conformalShadow_eq_conj_iff]

end GppHalfDensityDilation
