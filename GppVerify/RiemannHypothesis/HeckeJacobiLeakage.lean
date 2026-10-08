import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Hecke recurrence and the finite-support Jacobi leakage identity

Source: Codex handoff of 2026-10-08 (GPP-bridge PR #11 comment, "quantitative Hecke-boundary
inequality"), independently checked numerically before formalising.

For complex `z` put `a_m(z) = ∑_{j=0}^m e^{(m-2j)z}` (the symmetric-power character of the
two-eigenvalue Satake pair `p^{±z/log p}`). This file proves, with no hypothesis on `z`:

* `a_succ_add`: the three-term Hecke/Chebyshev recurrence `a_{m+2} + a_m = 2cosh z · a_{m+1}`
  with `a_0 = 1`, `a_1 = 2cosh z`;
* `sinh_mul_a`: the closed form `sinh z · a_m = sinh((m+1)z)`;
* `jacobi_residual_sq`: for the truncation `v = (a_0,…,a_M,0,…)` and the half-line Jacobi operator
  `(Jf)_m = f_{m-1} + f_{m+1}` (`f_{-1} = 0`), the residual of `J v = 2cosh z · v` is supported on
  `m = M, M+1` and `‖(J - 2cosh z) v‖² = |a_{M+1}|² + |a_M|²` exactly;
* `leakage_label`: at the arithmetic label `z = (ρ-1/2)·log p` the limiting leakage constant
  `2 sinh(2|Re z|)` equals `p^{2|Re ρ-1/2|} - p^{-2|Re ρ-1/2|}`.

## Scope (read this)

Only the exact finite algebra is proved. **Not proved here:** the spectral-distance inequality
`|a_{M+1}|²+|a_M|² ≥ dist(2cosh z,[-2,2])² ∑|a_m|²` (needs the spectrum of `J` on `ℓ²`), and the
limit `→ 2 sinh(2|Re z|)` (numerically confirmed at several `z`; the proof is an elementary
geometric-sum asymptotic not formalised here). Most importantly, nothing here says an actual
zeta zero's Hecke channel has vanishing leakage: that *zero-survival* step is missing and is
RH-strength. No RH claim.
-/

open Complex

namespace GppHeckeJacobiLeakage

/-- `a_m(z) = ∑_{j=0}^m e^{(m-2j)z}`. -/
noncomputable def a (z : ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (m + 1), Complex.exp (((m : ℂ) - 2 * j) * z)

theorem a_zero (z : ℂ) : a z 0 = 1 := by simp [a]

/-- `a_1 = 2cosh z`. -/
theorem a_one (z : ℂ) : a z 1 = 2 * Complex.cosh z := by
  simp only [a, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty]
  simp [Complex.cosh]
  ring_nf

/-- The three-term Hecke/Chebyshev recurrence `a_{m+2} + a_m = 2cosh z · a_{m+1}`. -/
theorem a_succ_add (z : ℂ) (m : ℕ) :
    a z (m + 2) + a z m = 2 * Complex.cosh z * a z (m + 1) := by
  have hterm : ∀ j : ℕ, 2 * Complex.cosh z * Complex.exp ((((m + 1 : ℕ) : ℂ) - 2 * j) * z)
      = Complex.exp ((((m + 2 : ℕ) : ℂ) - 2 * j) * z) + Complex.exp (((m : ℂ) - 2 * j) * z) := by
    intro j
    have h1 : (((m + 2 : ℕ) : ℂ) - 2 * j) * z = (((m + 1 : ℕ) : ℂ) - 2 * j) * z + z := by
      push_cast; ring
    have h2 : ((m : ℂ) - 2 * j) * z = (((m + 1 : ℕ) : ℂ) - 2 * j) * z + (-z) := by
      push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.cosh, Complex.exp_neg]
    field_simp
    try rw [Complex.exp_neg]
    try ring
  have hA : a z (m + 2) = (∑ j ∈ Finset.range (m + 2), Complex.exp ((((m + 2 : ℕ) : ℂ) - 2 * j) * z))
      + Complex.exp ((((m + 2 : ℕ) : ℂ) - 2 * (m + 2 : ℕ)) * z) := by
    unfold a; rw [Finset.sum_range_succ _ (m + 2)]
  have hC : (∑ j ∈ Finset.range (m + 2), Complex.exp (((m : ℂ) - 2 * j) * z))
      = a z m + Complex.exp (((m : ℂ) - 2 * (m + 1 : ℕ)) * z) := by
    unfold a; rw [Finset.sum_range_succ _ (m + 1)]
  have hlast : Complex.exp ((((m + 2 : ℕ) : ℂ) - 2 * (m + 2 : ℕ)) * z)
      = Complex.exp (((m : ℂ) - 2 * (m + 1 : ℕ)) * z) := by
    congr 1; push_cast; ring
  have hB : a z (m + 1) = ∑ j ∈ Finset.range (m + 2), Complex.exp ((((m + 1 : ℕ) : ℂ) - 2 * j) * z) := rfl
  rw [hB, Finset.mul_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib, hC]
  have : a z (m + 2) = (∑ j ∈ Finset.range (m + 2), Complex.exp ((((m + 2 : ℕ) : ℂ) - 2 * j) * z))
      + Complex.exp (((m : ℂ) - 2 * (m + 1 : ℕ)) * z) := by rw [hA, hlast]
  rw [this]; ring

/-- Closed form: `sinh z · a_m = sinh((m+1) z)`. -/
theorem sinh_mul_a (z : ℂ) (m : ℕ) :
    Complex.sinh z * a z m = Complex.sinh (((m : ℂ) + 1) * z) := by
  have key : ∀ j : ℕ, 2 * Complex.sinh z * Complex.exp (((m : ℂ) - 2 * j) * z)
      = Complex.exp (((m : ℂ) - 2 * j + 1) * z) - Complex.exp (((m : ℂ) - 2 * (j + 1 : ℕ) + 1) * z) := by
    intro j
    have h1 : ((m : ℂ) - 2 * j + 1) * z = ((m : ℂ) - 2 * j) * z + z := by ring
    have h2 : ((m : ℂ) - 2 * (j + 1 : ℕ) + 1) * z = ((m : ℂ) - 2 * j) * z + (-z) := by
      push_cast; ring
    rw [h1, h2, Complex.exp_add, Complex.exp_add, Complex.sinh, Complex.exp_neg]
    field_simp
    try rw [Complex.exp_neg]
    try ring
  have hsum : 2 * Complex.sinh z * a z m = Complex.exp (((m : ℂ) + 1) * z) - Complex.exp (-(((m : ℂ) + 1) * z)) := by
    unfold a
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => key j)]
    have := Finset.sum_range_sub' (fun j : ℕ => Complex.exp (((m : ℂ) - 2 * j + 1) * z)) (m + 1)
    rw [this]
    congr 1
    · simp
    · congr 1; push_cast; ring
  have h2 : (2 : ℂ) * Complex.sinh (((m : ℂ) + 1) * z)
      = Complex.exp (((m : ℂ) + 1) * z) - Complex.exp (-(((m : ℂ) + 1) * z)) := by
    rw [Complex.sinh]; ring
  have : (2 : ℂ) * (Complex.sinh z * a z m) = 2 * Complex.sinh (((m : ℂ) + 1) * z) := by
    rw [h2, ← hsum]; ring
  exact mul_left_cancel₀ two_ne_zero this

/-- The truncation `v = (a_0, …, a_M, 0, 0, …)`. -/
noncomputable def trunc (z : ℂ) (M : ℕ) (m : ℕ) : ℂ := if m ≤ M then a z m else 0

/-- Half-line Jacobi operator `(J f)_m = f_{m-1} + f_{m+1}` with `f_{-1} = 0`. -/
def jac (f : ℕ → ℂ) (m : ℕ) : ℂ := (if m = 0 then 0 else f (m - 1)) + f (m + 1)

/-- Residual of the eigen-equation for the truncation. -/
noncomputable def resid (z : ℂ) (M : ℕ) (m : ℕ) : ℂ :=
  jac (trunc z M) m - 2 * Complex.cosh z * trunc z M m

theorem resid_lt (z : ℂ) {M m : ℕ} (h : m < M) : resid z M m = 0 := by
  unfold resid jac trunc
  rcases m with _ | m
  · simp [show 0 ≤ M from Nat.zero_le _, show 1 ≤ M from h, a_zero, a_one]
  · have h1 : m + 1 ≤ M := h.le
    have h2 : m + 2 ≤ M := h
    have h3 : m ≤ M := by omega
    simp only [if_neg (Nat.succ_ne_zero m), Nat.succ_sub_one, if_pos h1, if_pos h2, if_pos h3]
    have := a_succ_add z m
    try simp only [Nat.add_sub_cancel]
    linear_combination this

theorem resid_eq (z : ℂ) (M : ℕ) : resid z M M = -a z (M + 1) := by
  unfold resid jac trunc
  have hM1 : ¬ (M + 1 ≤ M) := by omega
  rcases M with _ | M
  · simp [a_zero, a_one]
  · have h1 : M ≤ M + 1 := by omega
    simp only [if_neg (Nat.succ_ne_zero M), Nat.succ_sub_one, if_pos h1, if_pos le_rfl, if_neg hM1]
    have := a_succ_add z M
    linear_combination this

theorem resid_succ (z : ℂ) (M : ℕ) : resid z M (M + 1) = a z M := by
  unfold resid jac trunc
  have h1 : ¬ (M + 1 ≤ M) := by omega
  have h2 : ¬ (M + 2 ≤ M) := by omega
  simp [h1, h2]

theorem resid_gt (z : ℂ) {M m : ℕ} (h : M + 2 ≤ m) : resid z M m = 0 := by
  unfold resid jac trunc
  have h1 : ¬ (m ≤ M) := by omega
  have h2 : ¬ (m + 1 ≤ M) := by omega
  have h3 : ¬ (m - 1 ≤ M) := by omega
  have h4 : m ≠ 0 := by omega
  simp [h1, h2, h3, h4]

/-- **Exact leakage identity.** `‖(J - 2cosh z)v‖² = |a_{M+1}|² + |a_M|²`: the residual is
    supported on `{M, M+1}` and vanishes for `m ≥ M+2`, hence the full `ℓ²` norm equals the sum
    over `range (M+2)`. -/
theorem jacobi_residual_sq (z : ℂ) (M : ℕ) :
    ∑ m ∈ Finset.range (M + 2), Complex.normSq (resid z M m)
      = Complex.normSq (a z (M + 1)) + Complex.normSq (a z M) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, resid_succ, resid_eq]
  have : ∑ m ∈ Finset.range M, Complex.normSq (resid z M m) = 0 :=
    Finset.sum_eq_zero (fun m hm => by rw [resid_lt z (Finset.mem_range.mp hm)]; simp)
  rw [this, Complex.normSq_neg]; ring

/-- At the arithmetic label `z = (ρ - 1/2)·log p` the limiting leakage constant
    `2 sinh(2|Re z|)` is `p^{2d} - p^{-2d}` with `d = |Re ρ - 1/2|`. -/
theorem leakage_label (p d : ℝ) (hp : 0 < p) :
    2 * Real.sinh (2 * (d * Real.log p)) = p ^ (2 * d) - p ^ (-(2 * d)) := by
  rw [Real.sinh_eq, Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp]
  have e1 : Real.log p * (2 * d) = 2 * (d * Real.log p) := by ring
  have e2 : Real.log p * (-(2 * d)) = -(2 * (d * Real.log p)) := by ring
  rw [e1, e2]; ring

end GppHeckeJacobiLeakage
