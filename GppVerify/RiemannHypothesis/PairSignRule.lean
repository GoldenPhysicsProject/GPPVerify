import GppVerify.RiemannHypothesis.TwistorTwoModeThreshold

/-!
# The pair-sign rule for an off-line zero pair, and the lattice band algebra

Source: Grok S49 (`work/grok/2026-10-16_s49_fisher_margin_turan_laguerre.md`, Lean ask (b)) and S50
(`work/grok/2026-10-16_s50_laguerre_bands_gauss_lucas_turan.md`, Lean asks 2 and 3).

* `pair_sign_pos_iff`: for real `u, δ, γ`,
  `0 < Re (1/(u − (δ+iγ)²)²) ↔ 2|δ||γ| < |u + γ² − δ²|`; `pair_sign_nonpos_iff` is the complement.
  An off-line zero `ρ = ½+δ+iγ` of `ξ` contributes `1/(u−(ρ−½)²)²` to `−m'(u)`, and this says exactly
  where that contribution is negative (`|u + γ² − δ²| ≤ 2|δ|γ`).
* `pair_factor_identity`: with `a = α + iβ`, `D = (α − x)²`:
  `((a−x)² + t)(( ā−x)² + t) = (D + β²)² + 2(D − β²) t + t²` (the quartic pair factor of the zero form of
  the Laguerre inequalities).
* `lattice_band_iff`: `B² − 2M(M−1)B + M(M−1)(M−2)(M−3) < 0 ↔ |B − M(M−1)| < √(M(M−1)(4M−6))`.

**Scope.** Exact ring identities and a real quadratic inequality. The Laguerre generating identity
`|p(x+iy)|² = Σ L_n(x) y^{2n}` for polynomials, the lattice model, and the detection bands for actual
zeros are not formalized. No RH claim.
-/

namespace GppPairSignRule

open Complex

/-- Real part of `1/w²` is `≤ 0` iff `|Re w| ≤ |Im w|` (the complement of `re_inv_sq_pos_iff`). -/
theorem re_inv_sq_nonpos_iff (w : ℂ) : ((1 : ℂ) / w ^ 2).re ≤ 0 ↔ |w.re| ≤ |w.im| := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hn : 0 < Complex.normSq (w ^ 2) := Complex.normSq_pos.mpr (pow_ne_zero 2 hw)
  have hnum : (w ^ 2).re = w.re ^ 2 - w.im ^ 2 := by simp [pow_two]
  rw [one_div, Complex.inv_re, hnum, div_nonpos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · exact absurd h (not_le.mpr hn)
    · have : w.re ^ 2 ≤ w.im ^ 2 := by linarith
      exact sq_le_sq.mp this
  · intro h
    right
    have : w.re ^ 2 ≤ w.im ^ 2 := sq_le_sq.mpr h
    exact ⟨by linarith, hn.le⟩

/-- `u − (δ + iγ)²` has real part `u + γ² − δ²` and imaginary part `−2δγ`. -/
theorem shifted_parts (u δ γ : ℝ) :
    ((u : ℂ) - ((δ : ℂ) + γ * I) ^ 2).re = u + γ ^ 2 - δ ^ 2 ∧
      ((u : ℂ) - ((δ : ℂ) + γ * I) ^ 2).im = -(2 * δ * γ) := by
  constructor <;> simp [pow_two] <;> ring

/-- **Pair-sign rule.** The pair `ρ, 1 − ρ̄` of an off-line zero `½ + δ + iγ` contributes positively to
`−m'(u)` iff `2|δ||γ| < |u + γ² − δ²|`. -/
theorem pair_sign_pos_iff (u δ γ : ℝ) :
    0 < ((1 : ℂ) / ((u : ℂ) - ((δ : ℂ) + γ * I) ^ 2) ^ 2).re ↔
      2 * |δ| * |γ| < |u + γ ^ 2 - δ ^ 2| := by
  rw [GppTwistorTwoModeThreshold.re_inv_sq_pos_iff]
  obtain ⟨h1, h2⟩ := shifted_parts u δ γ
  rw [h1, h2, abs_neg, abs_mul, abs_mul, abs_two]

/-- The complement: the contribution is `≤ 0` iff `|u + γ² − δ²| ≤ 2|δ||γ|`. -/
theorem pair_sign_nonpos_iff (u δ γ : ℝ) :
    ((1 : ℂ) / ((u : ℂ) - ((δ : ℂ) + γ * I) ^ 2) ^ 2).re ≤ 0 ↔
      |u + γ ^ 2 - δ ^ 2| ≤ 2 * |δ| * |γ| := by
  rw [re_inv_sq_nonpos_iff]
  obtain ⟨h1, h2⟩ := shifted_parts u δ γ
  rw [h1, h2, abs_neg, abs_mul, abs_mul, abs_two]

/-- The quartic pair factor: for `a = α + iβ`, `D = (α − x)²`. -/
theorem pair_factor_identity (α β x t : ℝ) :
    (((α : ℂ) - x + β * I) ^ 2 + t) * (((α : ℂ) - x - β * I) ^ 2 + t) =
      (((α - x) ^ 2 + β ^ 2) ^ 2 + 2 * ((α - x) ^ 2 - β ^ 2) * t + t ^ 2 : ℝ) := by
  push_cast
  ring_nf
  simp only [I_sq, I_pow_four]
  ring

/-- Lattice band algebra: the quadratic in `B` is negative exactly on the band. -/
theorem lattice_band_iff (M B : ℝ) :
    B ^ 2 - 2 * M * (M - 1) * B + M * (M - 1) * (M - 2) * (M - 3) < 0 ↔
      |B - M * (M - 1)| < √(M * (M - 1) * (4 * M - 6)) := by
  have key : B ^ 2 - 2 * M * (M - 1) * B + M * (M - 1) * (M - 2) * (M - 3) =
      (B - M * (M - 1)) ^ 2 - M * (M - 1) * (4 * M - 6) := by ring
  rw [key, sub_neg, Real.lt_sqrt (abs_nonneg _), sq_abs]

end GppPairSignRule
