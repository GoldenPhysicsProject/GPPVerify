import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# The archimedean place is the one-dimensional celestial theory

In one fewer celestial dimension the boundary is a line, the conformal group is `SL(2,ℝ)`, the
principal series is `Δ = 1/2 + iν`, and the dilation generator is the operator `D` on `L²(0,∞)`
(modules `NymanBeurlingBoundStates`, `BoundStateRenormalization`, `PasterskiShaoNormalizability`).
This module identifies the archimedean factor of `ξ` with that theory, exactly:

* `mellin_gaussian`: the Gaussian `e^{-πx²}`, the self-dual ground state, has Mellin transform
  `(1/2) Γ_ℝ(s)` for `0 < re s`.
* `shadowCoeff s = Γ_ℝ(1-s)/Γ_ℝ(s)`: the local functional equation ratio, the shadow
  `Δ ↦ 1 - Δ` acting on a principal-series state. `gaussian_shadow_ratio`: it equals the ratio of
  Mellin transforms of the self-dual Gaussian at `1-s` and `s`.
* `zeta_eq_shadowCoeff_mul`: in the critical strip `ζ(s) = shadowCoeff(s) · ζ(1-s)`: the
  archimedean shadow coefficient is exactly the ratio of the arithmetic (prime) parts, which is the
  functional equation `Λ(1-s) = Λ(s)` read as a statement about the two halves.
* `norm_shadowCoeff_of_re_half`: on the principal series `re s = 1/2` the shadow coefficient has
  modulus `1`, because `1 - s = conj s`; the archimedean place is unitary there.

The primes enter through the Euler product, the other half of the adelic picture; that half has no
analogue in four-dimensional flat-space amplitudes.
-/

open Complex MeasureTheory Set Filter Topology

namespace GppArchimedeanCelestial

theorem mellin_exp_neg_pi {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) z = (Real.pi : ℂ) ^ (-z) * Gamma z := by
  unfold mellin
  have := integral_cpow_mul_exp_neg_mul_Ioi (a := z) (r := Real.pi) hz Real.pi_pos
  simp only [smul_eq_mul]
  have e : ∀ t : ℝ, ((Real.exp (-Real.pi * t) : ℝ) : ℂ) = Complex.exp (-(Real.pi * t)) := by
    intro t; push_cast; ring_nf
  simp_rw [e]
  rw [this, one_div, inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne), cpow_neg]

/-- **The Gaussian is the 1D celestial ground state, and its Mellin transform is `Γ_ℝ`.** -/
theorem mellin_gaussian {s : ℂ} (hs : 0 < s.re) :
    mellin (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) s = (1 / 2 : ℂ) * Gammaℝ s := by
  have h2 := mellin_comp_rpow (fun t : ℝ => (Real.exp (-Real.pi * t) : ℂ)) s 2
  have hf : (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) =
      fun t : ℝ => (fun u : ℝ => (Real.exp (-Real.pi * u) : ℂ)) (t ^ (2 : ℝ)) := by
    funext x; simp
  have h3 : (s / ((2 : ℝ) : ℂ)) = s / 2 := by push_cast; ring
  rw [hf, h2, h3, mellin_exp_neg_pi (by simp; linarith)]
  rw [Gammaℝ_def, Complex.real_smul, abs_two]
  push_cast
  have : -(s / 2) = -s / 2 := by ring
  rw [this]
  ring

/-- The shadow coefficient of the archimedean place: the local functional equation ratio
`Γ_ℝ(1-s)/Γ_ℝ(s)`, the 1D conformal shadow `Δ ↦ 1 - Δ` acting on a principal-series state. -/
noncomputable def shadowCoeff (s : ℂ) : ℂ := Gammaℝ (1 - s) / Gammaℝ s

/-- **Local functional equation of the Gaussian.** The Gaussian is its own Fourier transform, so its
Mellin transform at `1 - s` over its Mellin transform at `s` is the shadow coefficient. -/
theorem gaussian_shadow_ratio {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    mellin (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) (1 - s) /
      mellin (fun x : ℝ => (Real.exp (-Real.pi * x ^ 2) : ℂ)) s = shadowCoeff s := by
  rw [mellin_gaussian (by simp; linarith), mellin_gaussian h0, shadowCoeff]
  have : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  field_simp

/-- **The celestial shadow phase equals the arithmetic ratio.** In the critical strip,
`ζ(s) = shadowCoeff(s) · ζ(1-s)`: the archimedean shadow coefficient is exactly the ratio of the
arithmetic (prime) parts. -/
theorem zeta_eq_shadowCoeff_mul {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    riemannZeta s = shadowCoeff s * riemannZeta (1 - s) := by
  have hs0 : s ≠ 0 := by intro h; rw [h] at h0; simp at h0
  have hs1 : (1 - s) ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have g0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos h0
  have g1 : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero hs1, shadowCoeff,
    completedRiemannZeta_one_sub]
  field_simp

open ComplexConjugate in
theorem norm_gammaℝ_conj (s : ℂ) : ‖Gammaℝ (conj s)‖ = ‖Gammaℝ s‖ := by
  rw [Gammaℝ_def, Gammaℝ_def, norm_mul, norm_mul,
    norm_cpow_eq_rpow_re_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have e1 : (-conj s / 2).re = (-s / 2).re := by simp [div_ofNat_re]
  have e2 : conj s / 2 = conj (s / 2) := by
    rw [map_div₀]; congr 1; exact (map_ofNat (starRingEnd ℂ) 2).symm
  rw [e1, e2, Complex.Gamma_conj, Complex.norm_conj]

open ComplexConjugate in
/-- **Unitarity of the archimedean shadow on the principal series.** For `re s = 1/2`, the shadow
coefficient has modulus `1`: `1 - s = conj s`, so `Γ_ℝ(1-s)` and `Γ_ℝ(s)` have equal modulus. -/
theorem norm_shadowCoeff_of_re_half {s : ℂ} (h : s.re = 1 / 2) : ‖shadowCoeff s‖ = 1 := by
  have hc : 1 - s = conj s := by
    apply Complex.ext
    · simp [h]; linarith
    · simp
  have g0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [h]; norm_num)
  rw [shadowCoeff, hc, norm_div, norm_gammaℝ_conj, div_self (norm_ne_zero_iff.2 g0)]

/-- Off the line the shadow is not unitary-modulus in general, but the product identity is exact:
`‖ζ(s)‖ = ‖shadowCoeff s‖ ‖ζ(1-s)‖` in the strip. -/
theorem norm_zeta_eq_norm_shadow_mul {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ‖riemannZeta s‖ = ‖shadowCoeff s‖ * ‖riemannZeta (1 - s)‖ := by
  rw [zeta_eq_shadowCoeff_mul h0 h1, norm_mul]

#print axioms mellin_gaussian
#print axioms gaussian_shadow_ratio
#print axioms zeta_eq_shadowCoeff_mul
#print axioms norm_shadowCoeff_of_re_half

end GppArchimedeanCelestial
