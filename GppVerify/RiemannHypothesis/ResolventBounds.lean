import GppVerify.RiemannHypothesis.TwoSpaceForm
import GppVerify.RiemannHypothesis.RungZeroPositivity

/-!
# (O2): the sharp two-sided resolvent bounds for `Φ_p`

`Φ_p g = Σ_{m≥0} p^{−m/2} g(· − m log p)` satisfies, with `q = p^{−1/2}`,

  `‖g‖ / (1 + q)  ≤  ‖Φ_p g‖  ≤  ‖g‖ / (1 − q)`   (in `L²(ℝ)`),

including `p = 2` (`q = 2^{−1/2}`): `0.5857… ‖g‖ ≤ ‖Φ_2 g‖ ≤ 3.4142… ‖g‖`.

* **Resolvent identity** (`shiftSeries_resolvent`): `Φ(y) − q Φ(y − ℓ) = g(y)` pointwise — the shift series is
  the Neumann series of `(I − q T_ℓ)⁻¹`, `T_ℓ` the translation.
* **Upper bound** (`phiNormSq_le`): from the exact norm identity of `ShiftSeriesNorm`,
  `(1 − q²)‖Φ‖² = A(0) + 2Σ q^{k+1}A((k+1)ℓ)`, and `|A(x)| ≤ A(0)` (`abs_autocorr_le`):
  `(1 − q²)‖Φ‖² ≤ A(0)(1 + q)/(1 − q)`, i.e. `‖Φ‖² ≤ ‖g‖²/(1 − q)²`. No operator theory.
* **Lower bound** (`sq_le_phiNormSq`): `g = Φ − q T_ℓ Φ`, the pointwise inequality
  `(a − qb)² ≤ (1 + q)(a² + q b²)`, and translation invariance of `∫ Φ²`: `‖g‖² ≤ (1 + q)² ‖Φ‖²`.
  (The in-tree norm identity alone cannot give this at `p = 2`: `|A| ≤ A(0)` makes the lower estimate
  `A(0)(1 − 3q)/(1 − q)`, negative for `q > 1/3`.)
* `normSq_CN_le`: `‖C_N g‖² ≤ t_N(0) ‖g‖²` with `t_N(0) = Σ_{p≤N} (log p)(1 − p^{−1})/(1 − p^{−1/2})²`
  — the sharp raw upper bound used by the bounded `B_N`-completion (GPT's Theorem 6).

Analytic content as audited by Turbo (bridge `430236c`, Result B); this file is the Lean counterpart.
No `sorry`, no axiom.
-/

open MeasureTheory
open GppArithmeticReflection GppRungZeroPositivity
open scoped ContDiff

noncomputable section

namespace GppShiftPresentation

variable {g : ℝ → ℝ} {q ℓ : ℝ}

/-- **The resolvent identity** `(I − q T_ℓ) Φ = g`, pointwise. -/
theorem shiftSeries_resolvent (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) (y : ℝ) :
    shiftSeries q ℓ g y - q * shiftSeries q ℓ g (y - ℓ) = g y := by
  obtain ⟨B, hB⟩ := hg.bounded_above_of_compact_support hc
  have hs : ∀ z : ℝ, Summable (fun m : ℕ => q ^ m * g (z - m * ℓ)) := fun z => by
    refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hq0.le hq1).mul_right B)
      (fun m => ?_)
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0]
    have := hB (z - m * ℓ)
    simp only [Real.norm_eq_abs] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  unfold shiftSeries
  rw [(hs y).tsum_eq_zero_add, ← tsum_mul_left]
  have : ∀ m : ℕ, q ^ (m + 1) * g (y - ((m + 1 : ℕ) : ℝ) * ℓ) =
      q * (q ^ m * g (y - ℓ - m * ℓ)) := by
    intro m; push_cast; ring_nf
  simp only [this]
  simp

/-- **Upper bound:** `‖Φ‖² ≤ ‖g‖²/(1 − q)²`. -/
theorem integral_shiftSeries_sq_le (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ y, (shiftSeries q ℓ g y) ^ 2 ≤ (∫ y, g y ^ 2) / (1 - q) ^ 2 := by
  have hkey := norm_sq_shiftSeries (ℓ := ℓ) hg.continuous hc hq0 hq1
  have hne : (1 - q) ≠ 0 := by linarith
  have hA0 : autocorr g 0 = ∫ y, g y ^ 2 := autocorr_zero_eq g
  have hbd : ∀ k : ℕ, q ^ (k + 1) * autocorr g (((k : ℝ) + 1) * ℓ) ≤ q ^ (k + 1) * autocorr g 0 :=
    fun k => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_autocorr_le hg hc _))
      (by positivity)
  obtain ⟨C, hC⟩ := autocorr_bdd hg.continuous hc
  have hsum : Summable (fun k : ℕ => q ^ (k + 1) * autocorr g (((k : ℝ) + 1) * ℓ)) := by
    refine Summable.of_norm_bounded
      (((summable_geometric_of_lt_one hq0.le hq1).mul_left q).mul_right C) (fun k => ?_)
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hq0, pow_succ]
    calc q ^ k * q * |autocorr g (((k : ℝ) + 1) * ℓ)| ≤ q ^ k * q * C :=
          mul_le_mul_of_nonneg_left (hC _) (by positivity)
      _ = q * q ^ k * C := by ring
  have hgeo : Summable (fun k : ℕ => q ^ (k + 1) * autocorr g 0) :=
    ((summable_geometric_of_lt_one hq0.le hq1).mul_left q).mul_right (autocorr g 0) |>.congr
      (fun k => by ring)
  have hle : ∑' k : ℕ, q ^ (k + 1) * autocorr g (((k : ℝ) + 1) * ℓ) ≤
      ∑' k : ℕ, q ^ (k + 1) * autocorr g 0 := Summable.tsum_le_tsum hbd hsum hgeo
  have hgs : ∑' k : ℕ, q ^ (k + 1) * autocorr g 0 = autocorr g 0 * (q / (1 - q)) := by
    have : ∀ k : ℕ, q ^ (k + 1) * autocorr g 0 = (autocorr g 0 * q) * q ^ k := fun k => by ring
    simp_rw [this]
    rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    ring
  rw [hgs] at hle
  have h1 : (1 - q ^ 2) * ∫ y, (shiftSeries q ℓ g y) ^ 2 ≤
      autocorr g 0 * ((1 + q) / (1 - q)) := by
    rw [hkey]
    have : autocorr g 0 + 2 * (autocorr g 0 * (q / (1 - q))) = autocorr g 0 * ((1 + q) / (1 - q)) := by
      field_simp
      ring
    linarith
  have hpos : 0 < 1 - q ^ 2 := by nlinarith
  have hq' : 0 < 1 - q := by linarith
  rw [le_div_iff₀ (by positivity), ← hA0]
  set I := ∫ y, (shiftSeries q ℓ g y) ^ 2 with hI
  have hq2 : 0 < 1 + q := by linarith
  have h4 : I * (1 - q) ^ 2 * (1 + q) ≤ autocorr g 0 * (1 + q) := by
    calc I * (1 - q) ^ 2 * (1 + q) = (1 - q ^ 2) * I * (1 - q) := by ring
      _ ≤ autocorr g 0 * ((1 + q) / (1 - q)) * (1 - q) := mul_le_mul_of_nonneg_right h1 hq'.le
      _ = autocorr g 0 * (1 + q) := by field_simp
  exact le_of_mul_le_mul_right h4 hq2

/-- The pointwise comparison behind the lower bound: `(a − q b)² ≤ (1 + q)(a² + q b²)`. -/
theorem sq_sub_le (a b q : ℝ) (hq : 0 ≤ q) : (a - q * b) ^ 2 ≤ (1 + q) * (a ^ 2 + q * b ^ 2) := by
  nlinarith [mul_nonneg hq (sq_nonneg (a + b))]

/-- The abstract lower-bound step: if `g = Φ − q Φ(· − ℓ)` and `Φ²` is integrable, then
`∫ g² ≤ (1 + q)² ∫ Φ²`. -/
theorem integral_sq_le_of_resolvent {g Φ : ℝ → ℝ} {q ℓ : ℝ} (hq : 0 ≤ q)
    (hres : ∀ y, g y = Φ y - q * Φ (y - ℓ)) (hint : Integrable (fun y => Φ y ^ 2))
    (hg2 : Integrable (fun y => g y ^ 2)) :
    ∫ y, g y ^ 2 ≤ (1 + q) ^ 2 * ∫ y, Φ y ^ 2 := by
  have hintS : Integrable (fun y => Φ (y - ℓ) ^ 2) := hint.comp_sub_right ℓ
  have htr : ∫ y, Φ (y - ℓ) ^ 2 = ∫ y, Φ y ^ 2 :=
    integral_sub_right_eq_self (fun y => Φ y ^ 2) ℓ
  have hpt : ∀ y, g y ^ 2 ≤ (1 + q) * (Φ y ^ 2 + q * Φ (y - ℓ) ^ 2) := by
    intro y
    rw [hres y]
    exact sq_sub_le _ _ _ hq
  have hrhs : Integrable (fun y => (1 + q) * (Φ y ^ 2 + q * Φ (y - ℓ) ^ 2)) :=
    (hint.add (hintS.const_mul q)).const_mul (1 + q)
  have e : ∫ y, (1 + q) * (Φ y ^ 2 + q * Φ (y - ℓ) ^ 2) =
      (1 + q) * ((∫ y, Φ y ^ 2) + q * ∫ y, Φ (y - ℓ) ^ 2) := by
    rw [integral_const_mul (1 + q), integral_add hint (hintS.const_mul q), integral_const_mul q]
  calc ∫ y, g y ^ 2 ≤ ∫ y, (1 + q) * (Φ y ^ 2 + q * Φ (y - ℓ) ^ 2) := integral_mono hg2 hrhs hpt
    _ = (1 + q) ^ 2 * ∫ y, Φ y ^ 2 := by rw [e, htr]; ring

theorem integrable_sq_of_compact (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun y => g y ^ 2) := by
  have hcs : HasCompactSupport (fun y => g y ^ 2) :=
    hc.mono (fun y hy => by
      simp only [Function.mem_support, ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero,
        not_false_eq_true] at hy ⊢
      exact hy)
  exact (hg.pow 2).integrable_of_hasCompactSupport hcs

/-- **Lower bound:** `‖g‖² ≤ (1 + q)² ‖Φ‖²`. Valid for every `0 < q < 1`, in particular `q = 2^{−1/2}`. -/
theorem integral_sq_le_shiftSeries_sq (hg : Continuous g) (hc : HasCompactSupport g)
    (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ y, g y ^ 2 ≤ (1 + q) ^ 2 * ∫ y, (shiftSeries q ℓ g y) ^ 2 :=
  integral_sq_le_of_resolvent (g := g) (Φ := shiftSeries q ℓ g) (q := q) (ℓ := ℓ) hq0.le
    (fun y => (shiftSeries_resolvent (ℓ := ℓ) hg hc hq0 hq1 y).symm)
    (integrable_shiftSeries_sq hg hc hq0 hq1)
    (integrable_sq_of_compact hg hc)

/-! ### The bounds for `Φ_p` and for `C_N` -/

/-- **(O2), upper:** `‖Φ_p g‖² ≤ ‖g‖² / (1 − p^{−1/2})²`. -/
theorem phiNormSq_le {p : ℕ} (hp : 2 ≤ p) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    phiNormSq p g ≤ autocorr g 0 / (1 - qOf p) ^ 2 := by
  unfold phiNormSq
  rw [phi_eq hp, autocorr_zero_eq]
  exact integral_shiftSeries_sq_le hg hc (qOf_pos hp) (qOf_lt_one hp)

/-- **(O2), lower:** `‖g‖² ≤ (1 + p^{−1/2})² ‖Φ_p g‖²`, for every `p ≥ 2` including `p = 2`. -/
theorem sq_le_phiNormSq {p : ℕ} (hp : 2 ≤ p) {g : ℝ → ℝ} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    autocorr g 0 ≤ (1 + qOf p) ^ 2 * phiNormSq p g := by
  unfold phiNormSq
  rw [phi_eq hp, autocorr_zero_eq]
  exact integral_sq_le_shiftSeries_sq hg hc (qOf_pos hp) (qOf_lt_one hp)

/-- `t_N(0) = Σ_{p≤N} (log p)(1 − p^{−1}) / (1 − p^{−1/2})²`. -/
def tN0 (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, Real.log p * (1 - 1 / (p : ℝ)) / (1 - qOf p) ^ 2

/-- `(1 − p^{−1})/(1 − q)² = (1 + q)/(1 − q)`, since `p^{−1} = q²`. -/
theorem tN0_eq (N : ℕ) :
    tN0 N = ∑ p ∈ primesUpTo N, Real.log p * ((1 + qOf p) / (1 - qOf p)) := by
  unfold tN0
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have hq1 := qOf_lt_one hp2
  have hne : (1 - qOf p) ≠ 0 := by linarith
  have h2 : 1 - 1 / (p : ℝ) = (1 - qOf p) * (1 + qOf p) := by
    rw [← qOf_sq hp2]; ring
  rw [h2]
  field_simp

/-- **The sharp raw upper bound for `C_N`:** `‖C_N g‖² ≤ t_N(0) ‖g‖²`. -/
theorem normSq_CN_le (N : ℕ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ‖CN N hg.continuous hc‖ ^ 2 ≤ tN0 N * autocorr g 0 := by
  rw [normSq_CN]
  unfold shiftGramSum tN0
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1.le
  have hq : 0 ≤ 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hp1.le
    linarith
  have h := phiNormSq_le hp2 hg hc
  calc Real.log p * (1 - 1 / (p : ℝ)) * phiNormSq p g
      ≤ Real.log p * (1 - 1 / (p : ℝ)) * (autocorr g 0 / (1 - qOf p) ^ 2) :=
        mul_le_mul_of_nonneg_left h (mul_nonneg hlog hq)
    _ = Real.log p * (1 - 1 / (p : ℝ)) / (1 - qOf p) ^ 2 * autocorr g 0 := by ring

end GppShiftPresentation

#print axioms GppShiftPresentation.shiftSeries_resolvent
#print axioms GppShiftPresentation.integral_shiftSeries_sq_le
#print axioms GppShiftPresentation.integral_sq_le_shiftSeries_sq
#print axioms GppShiftPresentation.phiNormSq_le
#print axioms GppShiftPresentation.sq_le_phiNormSq
#print axioms GppShiftPresentation.tN0_eq
#print axioms GppShiftPresentation.normSq_CN_le
