import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-!
# Mellin–Plancherel on the line `Re s = 1/2`: the 1D delta-normalization of the principal series

Requested by Daniel Toupin / Golden Physics Project (2026-11-06): the physical massless
conformal basis is complete and delta-function normalizable exactly on the principal series
`Δ = d/2 + iν` (Pasterski–Shao, *A Conformal Basis for Flat Space Amplitudes*, §4.2 (4.7)–(4.9); the
citation is Astra's and has not been checked by this formalization). In boundary dimension one
this says that, on the line `Re s = 1/2`, the Mellin transform is an isometry up to `2π`.
Formalization: Claude Code.

* `schwartz_plancherel`: `∫ |𝓕 g|² = ∫ |g|²` for a Schwartz function `g : ℝ → ℂ`, from Mathlib's
  `L²` Plancherel isometry (`Lp.inner_fourier_eq`, `SchwartzMap.toLp_fourier_eq`).
* `halfline_norm_sq`: the change of variables `x = e^{-u}`,
  `∫_{x>0} |f(x)|² dx = ∫ e^{-u} |f(e^{-u})|² du`.
* `mellin_half_plancherel`: if `u ↦ e^{-u/2} f(e^{-u})` is a Schwartz function `g`, then
  `(1/2π) ∫ |𝓜f(1/2 + iτ)|² dτ = ∫_{x>0} |f(x)|² dx`.

**Scope.** Schwartz-class test functions only: the extension to all of `L²(ℝ₊, dx)`, the
statement that the Mellin transform is *onto* `L²(ℝ)` (completeness of the basis), the Klein–Gordon
inner product itself (and hence the physical meaning of the density), and the four-dimensional
`SL(2, ℂ)` version are NOT formalized. Nothing here says that any particular complex number, such
as a zero of the completed zeta function, is a point of this spectrum: that is the same question
as `Re s = 1/2` for it. No claim about RH.
-/

set_option autoImplicit false

namespace GppMellinPlancherel

open MeasureTheory SchwartzMap FourierTransform Set Real

theorem schwartz_plancherel (g : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ‖(𝓕 g) ξ‖ ^ 2 = ∫ u : ℝ, ‖g u‖ ^ 2 := by
  have h := MeasureTheory.Lp.inner_fourier_eq (g.toLp 2) (g.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq] at h
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  have e1 : ∀ᵐ a : ℝ, ((𝓕 g).toLp 2 : Lp ℂ 2) a = (𝓕 g) a := SchwartzMap.coeFn_toLp (𝓕 g) 2 volume
  have e2 : ∀ᵐ a : ℝ, ((g.toLp 2 : Lp ℂ 2)) a = g a := SchwartzMap.coeFn_toLp g 2 volume
  have h1 : ∫ a : ℝ, inner ℂ (((𝓕 g).toLp 2 : Lp ℂ 2) a) (((𝓕 g).toLp 2 : Lp ℂ 2) a)
      = ∫ a : ℝ, inner ℂ ((𝓕 g) a) ((𝓕 g) a) := by
    refine integral_congr_ae ?_
    filter_upwards [e1] with a ha
    rw [ha]
  have h2 : ∫ a : ℝ, inner ℂ ((g.toLp 2 : Lp ℂ 2) a) ((g.toLp 2 : Lp ℂ 2) a)
      = ∫ a : ℝ, inner ℂ (g a) (g a) := by
    refine integral_congr_ae ?_
    filter_upwards [e2] with a ha
    rw [ha]
  rw [h1, h2] at h
  simp only [inner_self_eq_norm_sq_to_K] at h
  have c1 := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := fun ξ : ℝ => ‖(𝓕 g) ξ‖ ^ 2)
  have c2 := integral_ofReal (𝕜 := ℂ) (μ := (volume : Measure ℝ)) (f := fun u : ℝ => ‖g u‖ ^ 2)
  push_cast at c1 c2
  rw [c1, c2] at h
  exact_mod_cast h

/-- change of variables x = e^{-u} on the half-line -/
theorem halfline_norm_sq (f : ℝ → ℂ) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ u : ℝ, Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
  have himg : (fun u : ℝ => Real.exp (-u)) '' (univ : Set ℝ) = Ioi 0 := by
    ext x
    simp only [mem_image, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨u, rfl⟩; exact Real.exp_pos _
    · intro hx; exact ⟨-Real.log x, by simp [Real.exp_log hx]⟩
  have hderiv : ∀ u ∈ (univ : Set ℝ),
      HasDerivWithinAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) univ u := by
    intro u _
    have h : HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-u)) u := by
      exact (hasDerivAt_neg u).exp.congr_deriv (by ring)
    exact h.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => Real.exp (-u)) univ := by
    intro a _ b _ h
    simpa using h
  have := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun x : ℝ => ‖f x‖ ^ 2)
  rw [himg] at this
  rw [this, setIntegral_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp [abs_of_neg, Real.exp_pos]

theorem mellin_half_plancherel (g : 𝓢(ℝ, ℂ)) (f : ℝ → ℂ)
    (hf : ∀ u : ℝ, (Real.exp (-(1 / 2) * u) : ℝ) • f (Real.exp (-u)) = g u) :
    (1 / (2 * Real.pi)) * ∫ τ : ℝ, ‖mellin f ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I)‖ ^ 2
      = ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 := by
  have hM : ∀ τ : ℝ, mellin f ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I) = (𝓕 g) (τ / (2 * Real.pi)) := by
    intro τ
    rw [mellin_eq_fourier]
    have hre : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).re = 1 / 2 := by simp
    have him : ((1 / 2 : ℂ) + (τ : ℂ) * Complex.I).im = τ := by simp
    rw [hre, him]
    have hfun : (fun u : ℝ => (Real.exp (-(1 / 2) * u) : ℝ) • f (Real.exp (-u))) = (g : ℝ → ℂ) := by
      funext u; exact hf u
    rw [hfun]
    rfl
  simp_rw [hM]
  have hscale := MeasureTheory.Measure.integral_comp_div (fun ξ : ℝ => ‖(𝓕 g) ξ‖ ^ 2) (2 * Real.pi)
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  simp only [abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), smul_eq_mul] at hscale
  rw [hscale, schwartz_plancherel g, halfline_norm_sq f]
  have hn : ∀ u : ℝ, ‖g u‖ ^ 2 = Real.exp (-u) * ‖f (Real.exp (-u))‖ ^ 2 := by
    intro u
    rw [← hf u, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← Real.exp_nat_mul]
    ring_nf
  simp_rw [hn]
  field_simp

end GppMellinPlancherel
