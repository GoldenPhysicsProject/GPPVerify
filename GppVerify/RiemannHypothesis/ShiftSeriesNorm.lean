import GppVerify.RiemannHypothesis.ArithmeticReflectionPositivity

/-!
# The shift series: `‖Σ_m q^m g(· − mℓ)‖²` in closed form

The analytic core of the per-prime identity of the final-identity candidate
(bridge `b38417e`, Turbo): for the canonical local map `Φ_p g = Σ_{m≥0} p^{−m/2} g(· − m log p)`,

  `(1 − q²) ‖Σ_m q^m g(· − mℓ)‖² = A(0) + 2 Σ_{k≥0} q^{k+1} A((k+1)ℓ)`,   `A = autocorr g`,

for a continuous compactly supported `g`, `ℓ > 0`, `0 < q < 1`. Stated for a *generic* shift `ℓ` and ratio
`q`; the prime specialisation `ℓ = log p`, `q = p^{−1/2}` is in `ShiftPresentation.lean`. Exact algebra
and measure theory only: no zeros, no positivity hypothesis, nothing about ARP.

Proof: `(Σ_m a_m)² = Σ_{(m,m')} a_m a_{m'}` (summable norms), `∫ Σ = Σ ∫` (summable integral norms), the
integral of the `(m, m')` term is `q^{m+m'} A((m' − m)ℓ)` (translation invariance); the double sum
`S` satisfies `S = R + q² S` by peeling off the row `m = 0` and the column `m' = 0`
(`T(m+1, m'+1) = q² T(m, m')`), with `R = A(0) + 2 Σ_k q^{k+1} A((k+1)ℓ)` (`A` even).

No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection

noncomputable section

namespace GppShiftPresentation

/-- The shift series `y ↦ Σ_{m≥0} q^m g(y − mℓ)`. -/
def shiftSeries (q ℓ : ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ := ∑' m : ℕ, q ^ m * g (y - m * ℓ)

variable {g : ℝ → ℝ} {q ℓ : ℝ}

/-- `autocorr` is even. -/
theorem autocorr_neg (g : ℝ → ℝ) (x : ℝ) : autocorr g (-x) = autocorr g x := by
  unfold autocorr
  have h := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => g y * g (y - x)) (-x)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [sub_neg_eq_add]
  rw [mul_comm]
  congr 2
  ring

theorem autocorr_bdd (hg : Continuous g) (hc : HasCompactSupport g) :
    ∃ C, ∀ x, |autocorr g x| ≤ C := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hc
  refine ⟨B * ∫ y, ‖g y‖, fun x => ?_⟩
  unfold autocorr
  have h1 : |∫ y, g y * g (y - x)| ≤ ∫ y, ‖g y * g (y - x)‖ := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => g y * g (y - x))
  refine h1.trans ?_
  have hint2 : Integrable (fun y => g (y - x)) := hint.comp_sub_right x
  have hm : Integrable (fun y => ‖g y * g (y - x)‖) := by
    refine Integrable.mono' (hint.norm.const_mul B) ?_ ?_
    · exact (hg.mul (hg.comp (continuous_id.sub continuous_const))).aestronglyMeasurable.norm
    · refine Filter.Eventually.of_forall fun y => ?_
      rw [norm_norm, norm_mul]
      have := hB (y - x)
      simp only [Real.norm_eq_abs] at this ⊢
      nlinarith [abs_nonneg (g y), abs_nonneg (g (y - x))]
  calc ∫ y, ‖g y * g (y - x)‖ ≤ ∫ y, B * ‖g y‖ := by
        refine integral_mono hm (hint.norm.const_mul B) fun y => ?_
        rw [norm_mul]
        have := hB (y - x)
        simp only [Real.norm_eq_abs] at this ⊢
        nlinarith [abs_nonneg (g y), abs_nonneg (g (y - x))]
    _ = B * ∫ y, ‖g y‖ := by rw [integral_const_mul]


/-! ### The double series -/

/-- The `(m, m')` term of the expansion of the square. -/
def term (q ℓ : ℝ) (g : ℝ → ℝ) (z : ℕ × ℕ) (y : ℝ) : ℝ :=
  (q ^ z.1 * g (y - z.1 * ℓ)) * (q ^ z.2 * g (y - z.2 * ℓ))

theorem term_integrable (hg : Continuous g) (hc : HasCompactSupport g) (z : ℕ × ℕ) :
    Integrable (term q ℓ g z) := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hc
  have h1 : Integrable (fun y => g (y - z.1 * ℓ)) := hint.comp_sub_right _
  have hmeas : AEStronglyMeasurable (fun y => g (y - z.2 * ℓ)) volume :=
    (hg.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have h2 := h1.bdd_mul (c := B) hmeas (Filter.Eventually.of_forall fun y => by
    simpa [Real.norm_eq_abs] using hB (y - z.2 * ℓ))
  have h3 := h2.const_mul (q ^ z.1 * q ^ z.2)
  refine h3.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [term]; ring

theorem term_integral (z : ℕ × ℕ) :
    ∫ y, term q ℓ g z y = q ^ (z.1 + z.2) * autocorr g ((z.2 - z.1 : ℝ) * ℓ) := by
  have h := integral_sub_right_eq_self (μ := volume)
    (fun y : ℝ => g y * g (y - ((z.2 : ℝ) - z.1) * ℓ)) ((z.1 : ℝ) * ℓ)
  have e : ∀ y, term q ℓ g z y =
      q ^ (z.1 + z.2) * ((fun y : ℝ => g y * g (y - ((z.2 : ℝ) - z.1) * ℓ)) (y - z.1 * ℓ)) := by
    intro y
    simp only [term, pow_add]
    have : y - z.1 * ℓ - ((z.2 : ℝ) - z.1) * ℓ = y - z.2 * ℓ := by ring
    rw [this]; ring
  simp_rw [e]
  rw [integral_const_mul, h]
  rfl

theorem term_norm_integral_le (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) :
    ∃ D : ℝ, ∀ z : ℕ × ℕ, ∫ y, ‖term q ℓ g z y‖ ≤ q ^ z.1 * q ^ z.2 * D := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hint : Integrable g := hg.integrable_of_hasCompactSupport hc
  refine ⟨B * ∫ y, ‖g y‖, fun z => ?_⟩
  have h1 : Integrable (fun y => ‖g (y - z.1 * ℓ)‖) := (hint.comp_sub_right _).norm
  have hI : Integrable (fun y => ‖term q ℓ g z y‖) := (term_integrable hg hc z).norm
  calc ∫ y, ‖term q ℓ g z y‖ ≤ ∫ y, q ^ z.1 * q ^ z.2 * (B * ‖g (y - z.1 * ℓ)‖) := by
        refine integral_mono hI ((h1.const_mul B).const_mul _) fun y => ?_
        simp only [term, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0]
        have := hB (y - z.2 * ℓ)
        simp only [Real.norm_eq_abs] at this
        have hq : 0 ≤ q ^ z.1 * q ^ z.2 := by positivity
        have h5 : |g (y - z.1 * ℓ)| * |g (y - z.2 * ℓ)| ≤ B * |g (y - z.1 * ℓ)| := by
          nlinarith [abs_nonneg (g (y - z.1 * ℓ))]
        calc q ^ z.1 * |g (y - z.1 * ℓ)| * (q ^ z.2 * |g (y - z.2 * ℓ)|)
            = q ^ z.1 * q ^ z.2 * (|g (y - z.1 * ℓ)| * |g (y - z.2 * ℓ)|) := by ring
          _ ≤ q ^ z.1 * q ^ z.2 * (B * |g (y - z.1 * ℓ)|) := mul_le_mul_of_nonneg_left h5 hq
    _ = q ^ z.1 * q ^ z.2 * (B * ∫ y, ‖g y‖) := by
        rw [integral_const_mul, integral_const_mul]
        have := integral_sub_right_eq_self (μ := volume) (fun y : ℝ => ‖g y‖) ((z.1 : ℝ) * ℓ)
        rw [this]


theorem summable_geom_pair (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (fun z : ℕ × ℕ => q ^ z.1 * q ^ z.2) := by
  have h : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0.le hq1
  exact Summable.mul_of_nonneg h h (fun _ => by positivity) (fun _ => by positivity)

/-- `(Σ_m a_m(y))² = Σ_{(m,m')} a_m(y) a_{m'}(y)` for the shift series. -/
theorem shiftSeries_sq (hg : Continuous g) (hc : HasCompactSupport g) (hq0 : 0 < q) (hq1 : q < 1)
    (y : ℝ) : (shiftSeries q ℓ g y) ^ 2 = ∑' z : ℕ × ℕ, term q ℓ g z y := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hs : Summable (fun m : ℕ => ‖q ^ m * g (y - m * ℓ)‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_)
      ((summable_geometric_of_lt_one hq0.le hq1).mul_right B)
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0]
    have := hB (y - m * ℓ)
    simp only [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  rw [sq, shiftSeries, tsum_mul_tsum_of_summable_norm hs hs]
  rfl

/-- **`∫ (shiftSeries)² = Σ_{(m,m')} q^{m+m'} A((m' − m)ℓ)`.** -/
theorem integral_shiftSeries_sq (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ y, (shiftSeries q ℓ g y) ^ 2 =
      ∑' z : ℕ × ℕ, q ^ (z.1 + z.2) * autocorr g ((z.2 - z.1 : ℝ) * ℓ) := by
  obtain ⟨D, hD⟩ := term_norm_integral_le (ℓ := ℓ) hg hc hq0
  have hsum : Summable fun z : ℕ × ℕ => ∫ y, ‖term q ℓ g z y‖ := by
    refine Summable.of_nonneg_of_le (fun z => integral_nonneg fun y => norm_nonneg _) hD ?_
    exact (summable_geom_pair hq0 hq1).mul_right D
  have h := integral_tsum_of_summable_integral_norm (fun z => term_integrable hg hc z) hsum
  simp_rw [shiftSeries_sq hg hc hq0 hq1, ← h]
  exact tsum_congr fun z => term_integral z


/-! ### Evaluating the double series -/

/-- **The double series, in closed form.** For an even bounded `A`,
`(1 − q²) Σ_{(m,m')} q^{m+m'} A((m' − m)ℓ) = A(0) + 2 Σ_k q^{k+1} A((k+1)ℓ)`. -/
theorem double_sum (A : ℝ → ℝ) (heven : ∀ x, A (-x) = A x) (C : ℝ) (hC : ∀ x, |A x| ≤ C)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - q ^ 2) * ∑' z : ℕ × ℕ, q ^ (z.1 + z.2) * A ((z.2 - z.1 : ℝ) * ℓ) =
      A 0 + 2 * ∑' k : ℕ, q ^ (k + 1) * A (((k : ℝ) + 1) * ℓ) := by
  set f : ℕ × ℕ → ℝ := fun z => q ^ (z.1 + z.2) * A ((z.2 - z.1 : ℝ) * ℓ) with hf
  have hgeom : Summable (fun m : ℕ => q ^ m) := summable_geometric_of_lt_one hq0.le hq1
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((summable_geom_pair hq0 hq1).mul_right C) (fun z => ?_)
    rw [hf]; simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0, pow_add]
    exact mul_le_mul_of_nonneg_left (hC _) (by positivity)
  have hrow : ∀ m, Summable fun c => f (m, c) := fun m => hfs.prod_factor m
  have hrowsum : Summable fun m => ∑' c, f (m, c) := hfs.prod
  -- column-zero terms
  have hcol : Summable fun m : ℕ => f (m + 1, 0) := by
    exact hfs.comp_injective (i := fun m : ℕ => (m + 1, 0)) (fun a b h => by simpa using h)
  have hrow0 : Summable fun c : ℕ => f (0, c) := hrow 0
  have hshift : ∀ m c : ℕ, f (m + 1, c + 1) = q ^ 2 * f (m, c) := by
    intro m c
    simp only [hf]
    have : (((c + 1 : ℕ) : ℝ) - ((m + 1 : ℕ) : ℝ)) = ((c : ℝ) - m) := by push_cast; ring
    rw [this]; ring
  have hrow_succ : ∀ m, ∑' c, f (m + 1, c) = f (m + 1, 0) + q ^ 2 * ∑' c, f (m, c) := by
    intro m
    rw [(hrow (m + 1)).tsum_eq_zero_add]
    simp_rw [hshift, tsum_mul_left]
  have hS : ∑' z, f z = ∑' m, ∑' c, f (m, c) := hfs.tsum_prod' hrow
  have h1 : ∑' m, ∑' c, f (m, c) = ∑' c, f (0, c) + ∑' m, ∑' c, f (m + 1, c) := by
    rw [hrowsum.tsum_eq_zero_add]
  have h2 : ∑' m, ∑' c, f (m + 1, c) = ∑' m, f (m + 1, 0) + q ^ 2 * ∑' m, ∑' c, f (m, c) := by
    simp_rw [hrow_succ]
    rw [Summable.tsum_add hcol (hrowsum.mul_left _), tsum_mul_left]
  have hr0 : ∑' c, f (0, c) = A 0 + ∑' k : ℕ, q ^ (k + 1) * A (((k : ℝ) + 1) * ℓ) := by
    rw [hrow0.tsum_eq_zero_add]
    congr 1
    · simp [hf]
    · refine tsum_congr fun k => ?_
      simp only [hf]; push_cast; ring_nf
  have hc0 : ∑' m : ℕ, f (m + 1, 0) = ∑' k : ℕ, q ^ (k + 1) * A (((k : ℝ) + 1) * ℓ) := by
    refine tsum_congr fun k => ?_
    simp only [hf]
    have : ((0 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) = -((k : ℝ) + 1) := by push_cast; ring
    have e2 : (((0 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ)) * ℓ = -(((k : ℝ) + 1) * ℓ) := by
      rw [this]; ring
    simp only [Nat.cast_zero] at e2 ⊢
    rw [e2, heven]
  have hkey := h1
  rw [h2, hr0, hc0] at hkey
  rw [hS]
  linear_combination hkey

/-- **The norm of the shift series.** `(1 − q²) ‖Σ_m q^m g(· − mℓ)‖² = A(0) + 2 Σ_k q^{k+1} A((k+1)ℓ)`,
`A = autocorr g`. -/
theorem norm_sq_shiftSeries (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) :
    (1 - q ^ 2) * ∫ y, (shiftSeries q ℓ g y) ^ 2 =
      autocorr g 0 + 2 * ∑' k : ℕ, q ^ (k + 1) * autocorr g (((k : ℝ) + 1) * ℓ) := by
  obtain ⟨C, hC⟩ := autocorr_bdd hg hc
  rw [integral_shiftSeries_sq hg hc hq0 hq1]
  exact double_sum (autocorr g) (autocorr_neg g) C hC hq0 hq1

end GppShiftPresentation

#print axioms GppShiftPresentation.norm_sq_shiftSeries
