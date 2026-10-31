import GppVerify.QuantumGravity.SinhWeierstrassProduct
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic

/-!
# The Gaussian vacuum partition function of the four-component arithmetic field

Source: Codex / Discovery2, `research/2026-09-27_arithmetic_free_field_holographic_ladder.md`
(`GPPDiscovery2`, `codex/discovery-workbench`), §§3–4. Daniel Toupin / Golden Physics Project, with AI
assistance from Codex (statements) and Claude Code (formalization).

The BPY variable is `Q = (1/2π) Σ_{n≥1} Σ_{a=1}^{4} G_{n,a}² / n²` with independent standard normal
`G_{n,a}`. This file proves the exact one-mode Laplace transform and the resulting limit of the
truncated vacuum partition function:

* `gaussian_laplace`: for `v > 0`, `t ≥ 0`,
  `∫ (2πv)^{-1/2} e^{−x²/(2v)} e^{−t x²} dx = (1 + 2tv)^{-1/2}`.
* `mode_laplace`: with `v = 1` and rate `t/(2π n²)`, one component contributes
  `(1 + t/(π n²))^{-1/2}`, so four components contribute `(1 + t/(π n²))^{-2}`.
* `partition_tendsto`: the partial products `∏_{n ≤ N} (1 + t/(π n²))^{-2}` converge to
  `(√(πt) / sinh √(πt))²` (via the existing Weierstrass product for `sinh`); with `t = πλ²` this is
  `(πλ / sinh πλ)²`, the squared celestial Plancherel weight.

**Scope.** The per-mode Gaussian integral and the limit of the product of per-mode transforms. The
construction of the cylindrical Gaussian measure on `ℓ²(ℕ)`, independence of the modes, the
identification with a Fredholm determinant `det(I + 2tC)^{-4/2}`, and the Mellin face
`E[Q^{s/2}] = 2ξ(s)` (§5) are not formalized. No claim about RH.
-/

set_option autoImplicit false

open Real Filter Topology MeasureTheory

namespace GppGaussianBpy

/-- One-mode Gaussian Laplace transform. -/
theorem gaussian_laplace (v t : ℝ) (hv : 0 < v) (ht : 0 ≤ t) :
    ∫ x : ℝ, (1 / Real.sqrt (2 * π * v)) * Real.exp (-x ^ 2 / (2 * v)) * Real.exp (-t * x ^ 2) =
      1 / Real.sqrt (1 + 2 * t * v) := by
  have hb : 0 < 1 / (2 * v) + t := by positivity
  have hrew : ∀ x : ℝ, (1 / Real.sqrt (2 * π * v)) * Real.exp (-x ^ 2 / (2 * v)) *
      Real.exp (-t * x ^ 2) =
      (1 / Real.sqrt (2 * π * v)) * Real.exp (-(1 / (2 * v) + t) * x ^ 2) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp_rw [hrew]
  rw [integral_const_mul, integral_gaussian]
  have h1 : π / (1 / (2 * v) + t) = (2 * π * v) / (1 + 2 * t * v) := by
    field_simp
  rw [h1, Real.sqrt_div (by positivity)]
  have hs : 0 < Real.sqrt (2 * π * v) := Real.sqrt_pos.mpr (by positivity)
  have hs2 : 0 < Real.sqrt (1 + 2 * t * v) := Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- One standard-normal component with rate `t/(2π n²)` contributes `(1 + t/(π n²))^{-1/2}`. -/
theorem mode_laplace (n t : ℝ) (hn : 0 < n) (ht : 0 ≤ t) :
    ∫ x : ℝ, (1 / Real.sqrt (2 * π * 1)) * Real.exp (-x ^ 2 / (2 * 1)) *
        Real.exp (-(t / (2 * π * n ^ 2)) * x ^ 2) = 1 / Real.sqrt (1 + t / (π * n ^ 2)) := by
  have h := gaussian_laplace 1 (t / (2 * π * n ^ 2)) one_pos (by positivity)
  rw [h]
  congr 2
  field_simp

/-- Four independent components contribute the fourth power: `(1/√x)^4 = (x⁻¹)^2` for `x > 0`. -/
theorem four_components (x : ℝ) (hx : 0 < x) : (1 / Real.sqrt x) ^ 4 = (x⁻¹) ^ 2 := by
  have : (1 / Real.sqrt x) ^ 4 = ((1 / Real.sqrt x) ^ 2) ^ 2 := by ring
  rw [this, div_pow, Real.sq_sqrt hx.le]
  simp

/-- **Partition function limit.** For `λ > 0` (so `t = πλ²`), the partial products of the per-mode
four-component transforms `(1 + λ²/n²)^{-2}` converge to `(πλ / sinh πλ)²`. -/
theorem partition_tendsto (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, ((1 + lam ^ 2 / ((j : ℝ) + 1) ^ 2)⁻¹) ^ 2)
      atTop (𝓝 ((π * lam / Real.sinh (π * lam)) ^ 2)) := by
  have hπl : 0 < π * lam := by positivity
  have hsinh : 0 < Real.sinh (π * lam) := by
    rw [Real.sinh_eq]
    have : Real.exp (-(π * lam)) < Real.exp (π * lam) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  have h := GppSinhWeierstrass.tendsto_prod_one_add_sq_div lam
  have hP : Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N, ((1 : ℝ) + lam ^ 2 / ((j : ℝ) + 1) ^ 2))
      atTop (𝓝 (Real.sinh (π * lam) / (π * lam))) := by
    have := h.div_const (π * lam)
    refine this.congr (fun N => ?_)
    field_simp
  have hS : Real.sinh (π * lam) / (π * lam) ≠ 0 := by positivity
  have hInv := (hP.inv₀ hS).pow 2
  rw [show (π * lam / Real.sinh (π * lam)) ^ 2 = (Real.sinh (π * lam) / (π * lam))⁻¹ ^ 2 by
    rw [inv_div]]
  refine hInv.congr (fun N => ?_)
  rw [Finset.prod_pow, Finset.prod_inv_distrib]

end GppGaussianBpy
