import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Wall/Krylov coefficients, the local prime Poisson identity, and the Dirichlet Green kernel

Source: Codex, GPP-bridge `research/codex/`:
* `2026-10-03_wall_krylov_shell_test.md` (commit `bd1c7cc`), §§1–4;
* `2026-10-02_endpoint_bpy_dirichlet_attack.md` (commit `a67c496`), §4.

**§1. Hankel/Jacobi coefficients.** For moments `μ₀, …, μ₄`:

* `hankel_three_det`: the `3 × 3` Hankel determinant is
  `Δ₃ = μ₀μ₂μ₄ + 2μ₁μ₂μ₃ − μ₀μ₃² − μ₁²μ₄ − μ₂³`;
* `hankel_two_shift`, `hankel_three_shift`: translating the spectral variable by `a`
  (moments `μ'_k = Σ_j C(k,j) a^{k−j} μ_j`) leaves `Δ₂` and `Δ₃` unchanged. So every Jacobi
  hopping coefficient `β_n = Δ_{n+1}Δ_{n−1}/Δ_n²` (for `n ≤ 2`) is invariant under the Casimir
  shift `K ↦ e^{−t}K`, which is the note's claim. Only the diagonal `α_n` move.
* `beta_one_eq_log_second`: `β₁ = (μ₀μ₂ − μ₁²)/μ₀²` with `μ₁ = −K'`, `μ₂ = K''` is
  `(K K'' − K'²)/K²`, which is `(log K)''`.

**§3. The local prime Poisson identity.** For `0 ≤ q < 1`:

* `hasSum_poisson_cos`: `Σ_{m≥0} q^m cos(mθ) = (1 − q cos θ)/(1 − 2q cos θ + q²)`;
* `poisson_series`: `1 + 2 Σ_{m≥1} q^m cos(mθ) = (1 − q²)/(1 − 2q cos θ + q²) = P_q(θ)`;
* `poisson_pos`: `P_q(θ) > 0`.

With `q = p^{-1/2}` and `θ = t log p`, the prime tower `Σ_{m≥1} (log p) p^{-m/2} cos(mt log p)`
is `(log p/2)(P_q − 1)`: half of a positive local delay, minus the vacuum. That is the note's
"vacuum-subtracted relative trace". §4's control radii `p^{-1/2 ± θ}` are `< 1` for
`0 < θ < ½`, so `poisson_pos` holds for them too. Local positivity cannot see the off-line
zeros of the control. That is the note's point, and it is consistent with this file.

**Endpoint BPY §4: the Dirichlet Green kernel** `G_D(x,y) = e^{−|x−y|/2} − e^{−(x+y)/2}` on
`x, y ≥ 0` is symmetric (`greenD_symm`), vanishes on the boundary (`greenD_zero_left`), and is
nonnegative (`greenD_nonneg`). `h(x) = e^{−x/2}` solves `h'' = h/4` (`exp_half_second_deriv`).
The Neumann correction `β̃ = β(|x|) − ½e^{−|x|/2}` has `β̃'(0+) = β'(0) + ¼`, which is `0` for the
seed's `β'(0) = −¼` (`neumann_correction`).

All of these were checked by hand against the notes; no corrections. §2's sign claim (a single
Gaussian prime-power term is negative) is immediate and not restated.

## Scope

Finite algebra, one power series, one kernel. The notes' targets — a finite
prime–Archimedean lossless network whose Wall coefficients are the arithmetic `β_n` — are not
constructed. No RH claim.
-/

namespace GppWallKrylov

/-- The `2 × 2` Hankel determinant. -/
def hankel2 (μ₀ μ₁ μ₂ : ℝ) : ℝ := !![μ₀, μ₁; μ₁, μ₂].det

/-- The `3 × 3` Hankel determinant. -/
def hankel3 (μ₀ μ₁ μ₂ μ₃ μ₄ : ℝ) : ℝ := !![μ₀, μ₁, μ₂; μ₁, μ₂, μ₃; μ₂, μ₃, μ₄].det

/-- `Δ₃ = μ₀μ₂μ₄ + 2μ₁μ₂μ₃ − μ₀μ₃² − μ₁²μ₄ − μ₂³`. -/
theorem hankel_three_det (μ₀ μ₁ μ₂ μ₃ μ₄ : ℝ) :
    hankel3 μ₀ μ₁ μ₂ μ₃ μ₄ =
      μ₀ * μ₂ * μ₄ + 2 * μ₁ * μ₂ * μ₃ - μ₀ * μ₃ ^ 2 - μ₁ ^ 2 * μ₄ - μ₂ ^ 3 := by
  rw [hankel3, Matrix.det_fin_three]; simp; ring

/-- **`Δ₂` is invariant under translation of the spectral variable.** -/
theorem hankel_two_shift (a μ₀ μ₁ μ₂ : ℝ) :
    hankel2 μ₀ (μ₁ + a * μ₀) (μ₂ + 2 * a * μ₁ + a ^ 2 * μ₀) = hankel2 μ₀ μ₁ μ₂ := by
  simp only [hankel2, Matrix.det_fin_two_of]; ring

/-- **`Δ₃` is invariant under translation of the spectral variable.** -/
theorem hankel_three_shift (a μ₀ μ₁ μ₂ μ₃ μ₄ : ℝ) :
    hankel3 μ₀ (μ₁ + a * μ₀) (μ₂ + 2 * a * μ₁ + a ^ 2 * μ₀)
        (μ₃ + 3 * a * μ₂ + 3 * a ^ 2 * μ₁ + a ^ 3 * μ₀)
        (μ₄ + 4 * a * μ₃ + 6 * a ^ 2 * μ₂ + 4 * a ^ 3 * μ₁ + a ^ 4 * μ₀) =
      hankel3 μ₀ μ₁ μ₂ μ₃ μ₄ := by
  rw [hankel_three_det, hankel_three_det]; ring

/-- `β₁ = Δ₂/μ₀²` with `μ₀ = K`, `μ₁ = −K'`, `μ₂ = K''` is `(K K'' − K'²)/K²`. -/
theorem beta_one_eq_log_second (K K' K'' : ℝ) :
    hankel2 K (-K') K'' / K ^ 2 = (K * K'' - K' ^ 2) / K ^ 2 := by
  simp only [hankel2, Matrix.det_fin_two_of]; ring

/-- `Σ_{m≥0} q^m cos(mθ) = (1 − q cos θ)/(1 − 2q cos θ + q²)` for `0 ≤ q < 1`. -/
theorem hasSum_poisson_cos (q θ : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => q ^ m * Real.cos (m * θ))
      ((1 - q * Real.cos θ) / (1 - 2 * q * Real.cos θ + q ^ 2)) := by
  set w : ℂ := q * Complex.exp (θ * Complex.I) with hw
  have hnorm : ‖w‖ < 1 := by
    rw [hw, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hq0]
    exact hq1
  have hg := (hasSum_geometric_of_norm_lt_one hnorm).mapL Complex.reCLM
  have hterm : ∀ m : ℕ, Complex.reCLM (w ^ m) = q ^ m * Real.cos (m * θ) := by
    intro m
    rw [hw, mul_pow, ← Complex.exp_nat_mul, Complex.reCLM_apply]
    have : (m : ℂ) * (θ * Complex.I) = ((m * θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp only [hterm] at hg
  convert hg using 1
  have hden : 1 - 2 * q * Real.cos θ + q ^ 2 ≠ 0 := by
    have : 0 < 1 - 2 * q * Real.cos θ + q ^ 2 := by
      nlinarith [Real.cos_le_one θ, sq_nonneg (q - 1), mul_nonneg hq0 (sub_nonneg.mpr
        (Real.cos_le_one θ))]
    exact this.ne'
  rw [Complex.reCLM_apply, Complex.inv_re, Complex.normSq_apply]
  simp only [hw, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
    Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  have hsc := Real.sin_sq_add_cos_sq θ
  have hden' : (1 - q * Real.cos θ) * (1 - q * Real.cos θ) + (0 - q * Real.sin θ) *
      (0 - q * Real.sin θ) = 1 - 2 * q * Real.cos θ + q ^ 2 := by
    linear_combination q ^ 2 * hsc
  rw [hden']

/-- **The Poisson series.** `1 + 2 Σ_{m≥1} q^m cos(mθ) = (1 − q²)/(1 − 2q cos θ + q²)`. -/
theorem poisson_series (q θ : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun m : ℕ => 2 * (q ^ (m + 1) * Real.cos ((m + 1 : ℕ) * θ)))
      ((1 - q ^ 2) / (1 - 2 * q * Real.cos θ + q ^ 2) - 1) := by
  have h := (hasSum_nat_add_iff' 1).mpr (hasSum_poisson_cos q θ hq0 hq1)
  have h2 := h.mul_left 2
  have hden : 0 < 1 - 2 * q * Real.cos θ + q ^ 2 := by
    nlinarith [Real.cos_le_one θ, sq_nonneg (q - 1), mul_nonneg hq0 (sub_nonneg.mpr
      (Real.cos_le_one θ))]
  have e : (1 - q ^ 2) / (1 - 2 * q * Real.cos θ + q ^ 2) - 1 =
      2 * ((1 - q * Real.cos θ) / (1 - 2 * q * Real.cos θ + q ^ 2) -
        ∑ i ∈ Finset.range 1, q ^ i * Real.cos (↑i * θ)) := by
    have hs : ∑ i ∈ Finset.range 1, q ^ i * Real.cos (↑i * θ) = 1 := by simp
    rw [hs, div_sub_one hden.ne', div_sub_one hden.ne', mul_div_assoc']
    congr 1; ring
  rw [e]; exact h2

/-- **The Poisson kernel is positive** for `0 ≤ q < 1`. -/
theorem poisson_pos (q θ : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    0 < (1 - q ^ 2) / (1 - 2 * q * Real.cos θ + q ^ 2) := by
  have hden : 0 < 1 - 2 * q * Real.cos θ + q ^ 2 := by
    nlinarith [Real.cos_le_one θ, sq_nonneg (q - 1), mul_nonneg hq0 (sub_nonneg.mpr
      (Real.cos_le_one θ))]
  apply div_pos _ hden
  nlinarith

/-- The Dirichlet Green kernel `G_D(x,y) = e^{−|x−y|/2} − e^{−(x+y)/2}`. -/
noncomputable def greenD (x y : ℝ) : ℝ := Real.exp (-|x - y| / 2) - Real.exp (-(x + y) / 2)

theorem greenD_symm (x y : ℝ) : greenD x y = greenD y x := by
  simp only [greenD, abs_sub_comm, add_comm]

/-- `G_D` vanishes on the boundary `x = 0` (for `y ≥ 0`). -/
theorem greenD_zero_left (y : ℝ) (hy : 0 ≤ y) : greenD 0 y = 0 := by
  simp only [greenD, zero_sub, abs_neg, abs_of_nonneg hy, zero_add, sub_self]

/-- `G_D ≥ 0` on the quadrant `x, y ≥ 0`. -/
theorem greenD_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ greenD x y := by
  simp only [greenD, sub_nonneg]
  apply Real.exp_le_exp.mpr
  have : |x - y| ≤ x + y := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  linarith

/-- `h(x) = e^{−x/2}` satisfies `h'' = h/4`. -/
theorem exp_half_second_deriv (x : ℝ) :
    HasDerivAt (fun x => -(1 / 2) * Real.exp (-x / 2)) (1 / 4 * Real.exp (-x / 2)) x := by
  have h : HasDerivAt (fun x : ℝ => -x / 2) (-1 / 2) x := by
    simpa using (hasDerivAt_id x).neg.div_const 2
  have := (h.exp).const_mul (-(1 / 2))
  have e : (1 / 4 : ℝ) * Real.exp (-x / 2) = -(1 / 2) * (Real.exp (-x / 2) * (-1 / 2)) := by ring
  rw [e]; exact this

/-- **The Neumann correction cancels the derivative at `0`.** If `β'(0) = −¼`, then
`β̃ = β − ½e^{−x/2}` has `β̃'(0) = β'(0) − ½ · (−½) = 0`. -/
theorem neumann_correction (β₀' : ℝ) (h : β₀' = -1 / 4) :
    β₀' - 1 / 2 * (-(1 / 2) * Real.exp (-0 / 2)) = 0 := by
  rw [h]; simp; norm_num

end GppWallKrylov
