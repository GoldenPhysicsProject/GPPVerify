import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import GppVerify.QuantumGravity.SinhWeierstrassProduct

/-!
# Four-component rigidity: completed zeta selects four Gaussian components

Source: Codex, GPPDiscovery2 `codex/discovery-workbench`,
`research/2026-09-27_four_component_gaussian_rigidity.md` (commit `af7e68a`) and its
checker `DiscoveryLean/FourComponentRigidity.lean` (`06dc648`).

The note considers the squared radius of a `d`-component Gaussian field on the positive
number-circle modes,
`Q_d = (1/2π) Σ_{a ≤ d} Σ_{n ≥ 1} G_{n,a}² / n²`, with independent standard real Gaussians,
and makes two claims.

1. **One moment forces `d = 4`.** `E Q_d = (d/2π) ζ(2) = dπ/12` and `2ξ(2) = π/3`, so the single
   moment condition `E Q_d = 2ξ(2)` holds iff `d = 4`.
2. **Laplace transform.** `E e^{-t Q_d} = ∏_{n≥1} (1 + t/(πn²))^{-d/2}
   = (√(πt) / sinh √(πt))^{d/2}`, which at `t = πλ²` is `P(λ)^{d/2}` with
   `P(λ) = πλ / sinh πλ`.

This file proves the deterministic content of both, from Mathlib's `ζ(2) = π²/6` and the Euler
sine product. Codex's checker assumed the two constants `dπ/12` and `π/3` as inputs; here they
are derived:

* `completedRiemannZeta_two`: `Λ(2) = π/6`, so `two_xi_two`: `2ξ(2) = π/3` with
  `ξ(s) = ½ s(s−1) Λ(s)`.
* `mean_radius`: `(d/2π) ζ(2) = dπ/12`.
* `component_count_forced`: `(d/2π) ζ(2) = 2ξ(2) ↔ d = 4`.
* `tendsto_laplace_product`: the partial products of `1 + t/(πn²)` converge to
  `sinh √(πt) / √(πt)` for `t > 0`.
* `tendsto_laplace_product_rpow`: their `−d/2` powers converge to `(√(πt)/sinh √(πt))^{d/2}`.
* `laplace_at_pi_sq`: at `t = πλ²` (`λ > 0`) the limit is `(πλ / sinh πλ)^{d/2}`.

## Scope

The probabilistic steps are not formalized: the one-mode Gaussian Laplace transform
`E e^{-tG²/(2πn²)} = (1 + t/(πn²))^{-1/2}`, independence, and the interchange of expectation
with the infinite sum and product. Nor is the full BPY identity `E[Q_4^{s/2}] = 2ξ(s)`. As the
note itself says, the component count `4` is a property of this Gaussian ansatz. Identifying it
with a spacetime dimension would need a further reconstruction theorem, which is not claimed.
-/

open Filter Topology

namespace GppFourComponentRigidity

/-- Riemann's `ξ(s) = ½ s (s − 1) Λ(s)`, with `Λ = completedRiemannZeta`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta s

/-- `Γ_ℝ(2) = π⁻¹`. -/
theorem Gammaℝ_two : Complex.Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
  rw [Complex.Gammaℝ, show -(2 : ℂ) / 2 = -1 by norm_num, show (2 : ℂ) / 2 = 1 by norm_num,
    Complex.Gamma_one, mul_one, Complex.cpow_neg_one]

/-- `Λ(2) = π/6`. -/
theorem completedRiemannZeta_two : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
  have h := riemannZeta_def_of_ne_zero (s := 2) two_ne_zero
  rw [riemannZeta_two, Gammaℝ_two] at h
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [div_inv_eq_mul] at h
  have : completedRiemannZeta 2 = (Real.pi : ℂ) ^ 2 / 6 / Real.pi := by
    rw [h]; field_simp
  rw [this]; field_simp

/-- `2ξ(2) = π/3`. -/
theorem two_xi_two : 2 * xi 2 = (Real.pi : ℂ) / 3 := by
  rw [xi, completedRiemannZeta_two]; ring

/-- The mean squared radius: `(d/2π) ζ(2) = dπ/12`. -/
theorem mean_radius (d : ℝ) :
    (d : ℂ) / (2 * Real.pi) * riemannZeta 2 = (d : ℂ) * Real.pi / 12 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [riemannZeta_two]; field_simp; ring

/-- **Four-component rigidity.** The single BPY moment condition `E Q_d = 2ξ(2)` holds
exactly when `d = 4`. -/
theorem component_count_forced (d : ℝ) :
    (d : ℂ) / (2 * Real.pi) * riemannZeta 2 = 2 * xi 2 ↔ d = 4 := by
  rw [mean_radius, two_xi_two]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · intro h
    have h' : (d : ℂ) = 4 := by
      have := congrArg (· * (12 / (Real.pi : ℂ))) h
      field_simp at this
      linear_combination this / 3
    exact_mod_cast h'
  · rintro rfl; push_cast; ring

/-- `√(πt) = π √(t/π)`. -/
theorem sqrt_pi_mul (t : ℝ) :
    Real.sqrt (Real.pi * t) = Real.pi * Real.sqrt (t / Real.pi) := by
  have hpi := Real.pi_pos
  rw [show Real.pi * t = Real.pi ^ 2 * (t / Real.pi) by field_simp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpi.le]

/-- **The Laplace-transform product.** For `t > 0`, the partial products of
`1 + t/(πn²)` converge to `sinh √(πt) / √(πt)`. -/
theorem tendsto_laplace_product (t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ => ∏ j ∈ Finset.range n, (1 + t / (Real.pi * ((j : ℝ) + 1) ^ 2)))
      atTop (𝓝 (Real.sinh (Real.sqrt (Real.pi * t)) / Real.sqrt (Real.pi * t))) := by
  set a := Real.sqrt (t / Real.pi) with ha
  have hpi := Real.pi_pos
  have ha_pos : 0 < a := Real.sqrt_pos.mpr (div_pos ht hpi)
  have ha2 : a ^ 2 = t / Real.pi := Real.sq_sqrt (div_pos ht hpi).le
  have hc : Real.pi * a ≠ 0 := (mul_pos hpi ha_pos).ne'
  have h := (GppSinhWeierstrass.tendsto_prod_one_add_sq_div a).div_const (Real.pi * a)
  rw [sqrt_pi_mul t, ← ha]
  refine h.congr (fun n => ?_)
  rw [mul_div_cancel_left₀ _ hc]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [ha2]
  have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- `sinh x / x > 0` for `x > 0`. -/
theorem sinh_div_pos {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x / x :=
  div_pos (Real.sinh_pos_iff.mpr hx) hx

/-- **The `d`-component Laplace transform.** The `−d/2` powers of the partial products
converge to `(√(πt) / sinh √(πt))^{d/2}`. -/
theorem tendsto_laplace_product_rpow (d t : ℝ) (ht : 0 < t) :
    Tendsto (fun n : ℕ =>
        (∏ j ∈ Finset.range n, (1 + t / (Real.pi * ((j : ℝ) + 1) ^ 2))) ^ (-(d / 2)))
      atTop (𝓝 ((Real.sqrt (Real.pi * t) / Real.sinh (Real.sqrt (Real.pi * t))) ^ (d / 2))) := by
  have hs : 0 < Real.sqrt (Real.pi * t) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos ht)
  have hL := sinh_div_pos hs
  have h := (tendsto_laplace_product t ht).rpow_const (p := -(d / 2)) (Or.inl hL.ne')
  convert h using 2
  rw [Real.rpow_neg hL.le, ← Real.inv_rpow hL.le, inv_div]

/-- At `t = πλ²` the `d`-component limit is `P(λ)^{d/2}` with `P(λ) = πλ / sinh πλ`; for
`d = 4` this is `P(λ)²`, the BPY case. -/
theorem laplace_at_pi_sq (d lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun n : ℕ =>
        (∏ j ∈ Finset.range n,
          (1 + Real.pi * lam ^ 2 / (Real.pi * ((j : ℝ) + 1) ^ 2))) ^ (-(d / 2)))
      atTop (𝓝 ((Real.pi * lam / Real.sinh (Real.pi * lam)) ^ (d / 2))) := by
  have ht : 0 < Real.pi * lam ^ 2 := by positivity
  have hs : Real.sqrt (Real.pi * (Real.pi * lam ^ 2)) = Real.pi * lam := by
    rw [show Real.pi * (Real.pi * lam ^ 2) = (Real.pi * lam) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  have h := tendsto_laplace_product_rpow d (Real.pi * lam ^ 2) ht
  rwa [hs] at h

end GppFourComponentRigidity
