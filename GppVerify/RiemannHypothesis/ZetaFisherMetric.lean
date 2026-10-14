import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.MeanInequalities

/-!
# The zeta Gibbs Fisher metric: `(log ζ)''(β) = Var_β(log N) > 0`

Source: Codex, GPPDiscovery2 `research/2026-09-27_zeta_coherent_state_ads2_geometry.md` §3
(branch `codex/discovery-workbench`). The quantum-information metric of the arithmetic coherent states
is `g = (d²/dβ²) log ζ(β)` with `β = 2σ`, and it equals the variance of `log N` under the zeta Gibbs
law `P_β(n) = n^{−β}/ζ(β)`.

For real `β > 1` write `Z(β) = Σ_{n≥1} n^{−β}`, `M₁ = Σ (log n) n^{−β}`, `M₂ = Σ (log n)² n^{−β}`.
This file proves:
* `hasDerivAt_Z`, `hasDerivAt_M1`: `Z' = −M₁` and `M₁' = −M₂` (termwise, on `(1, ∞)`).
* `hasDerivAt_logderiv`: the logarithmic derivative `D = −M₁/Z` has derivative
  `(Z M₂ − M₁²)/Z²`. That is `(log Z)'' = E[(log N)²] − E[log N]² = Var_β(log N)`.
* `fisher_pos`: `Z M₂ − M₁² > 0`, so the Fisher metric is **strictly positive** for every `β > 1`.
  The proof is Cauchy–Schwarz (Hölder with `p = q = 2`), and strictness holds because `log N` is not
  constant.

**Not formalized:** the pole asymptotics `(log ζ)''(1 + δ) = 1/δ² + O(1)` (the AdS₂ boundary of the
note, §§4–5); see the PR for a numerical check. Positivity of the Fisher metric uses only the
positivity of the Dirichlet coefficients, so it also holds for the shifted fake
`ζ(s−θ)ζ(s+θ)`. It is **not** an RH mechanism. **No RH claim.**
-/

namespace GppZetaFisherMetric

open Real Filter Topology Set

/-- `L n = log(n + 1)`. -/
noncomputable def L (n : ℕ) : ℝ := Real.log ((n : ℝ) + 1)

/-- The term `(n+1)^{−β} = exp(−β L n)`. -/
noncomputable def term (n : ℕ) (β : ℝ) : ℝ := Real.exp (-β * L n)

theorem L_nonneg (n : ℕ) : 0 ≤ L n := Real.log_nonneg (by have := n.cast_nonneg (α := ℝ); linarith)

theorem term_eq (n : ℕ) (β : ℝ) : term n β = ((n : ℝ) + 1) ^ (-β) := by
  unfold term L
  rw [Real.rpow_def_of_pos (by positivity)]; ring_nf

/-- `Z(β) = Σ (n+1)^{−β}`, `M₁ = Σ L·term`, `M₂ = Σ L²·term`. -/
noncomputable def Z (β : ℝ) : ℝ := ∑' n, term n β
noncomputable def M1 (β : ℝ) : ℝ := ∑' n, L n * term n β
noncomputable def M2 (β : ℝ) : ℝ := ∑' n, L n ^ 2 * term n β

/-- `L n ≤ (n+1)^ε / ε` for `ε > 0`. -/
theorem L_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) : L n ≤ ((n : ℝ) + 1) ^ ε / ε := by
  unfold L
  exact Real.log_le_rpow_div (by positivity) hε

/-- The dominating series `(log(n+1))^k (n+1)^{−a}` is summable for `a > 1`. -/
theorem summable_Lpow_term (k : ℕ) {a : ℝ} (ha : 1 < a) :
    Summable fun n => L n ^ k * term n a := by
  set ε := (a - 1) / (2 * (k + 1)) with hεdef
  have hε : 0 < ε := by rw [hεdef]; apply div_pos <;> [linarith; positivity]
  have hexp : -a + k * ε < -1 := by
    rw [hεdef]
    have hk : (0 : ℝ) < k + 1 := by positivity
    have : (k : ℝ) * ((a - 1) / (2 * (k + 1))) ≤ (a - 1) / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-a + k * ε) := by
    have := Real.summable_nat_rpow.mpr hexp
    exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (L_nonneg n) k)
    (Real.exp_pos _).le) (fun n => ?_) (hsum.mul_left (ε⁻¹ ^ k))
  have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc L n ^ k * term n a ≤ (((n : ℝ) + 1) ^ ε / ε) ^ k * term n a := by
        gcongr
        · exact (Real.exp_pos _).le
        · exact L_nonneg n
        · exact L_le n hε
    _ = ε⁻¹ ^ k * ((n : ℝ) + 1) ^ (-a + k * ε) := by
        rw [term_eq, div_eq_mul_inv, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hb.le,
          Real.rpow_add hb]
        ring_nf

/-- Termwise derivative of `L^k · term`. -/
theorem hasDerivAt_Lterm (k n : ℕ) (β : ℝ) :
    HasDerivAt (fun y => L n ^ k * term n y) (-(L n ^ (k + 1) * term n β)) β := by
  unfold term
  have h := ((hasDerivAt_id β).neg.mul_const (L n)).exp.const_mul (L n ^ k)
  refine (h.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  · simp only [Pi.neg_apply, id]; ring
  · simp only [Pi.neg_apply, id]

theorem term_pos (n : ℕ) (β : ℝ) : 0 < term n β := Real.exp_pos _

theorem term_le_of_le (n : ℕ) {a y : ℝ} (hy : a ≤ y) : term n y ≤ term n a := by
  unfold term
  exact Real.exp_le_exp.mpr (by nlinarith [L_nonneg n])

/-- Generic termwise differentiation of `Σ L^k · term` on `(a, ∞)`, `a > 1`. -/
theorem hasDerivAt_sum (k : ℕ) {β : ℝ} (hβ : 1 < β) :
    HasDerivAt (fun y => ∑' n, L n ^ k * term n y) (-(∑' n, L n ^ (k + 1) * term n β)) β := by
  set a := (1 + β) / 2 with hadef
  have ha : 1 < a := by rw [hadef]; linarith
  have haβ : a < β := by rw [hadef]; linarith
  have h := hasDerivAt_tsum_of_isPreconnected (t := Ioi a) (y₀ := β)
    (g := fun n y => L n ^ k * term n y) (g' := fun n y => -(L n ^ (k + 1) * term n y))
    (summable_Lpow_term (k + 1) ha) isOpen_Ioi (isPreconnected_Ioi)
    (fun n y _ => hasDerivAt_Lterm k n y)
    (fun n y hy => by
      rw [norm_neg, Real.norm_of_nonneg (mul_nonneg (pow_nonneg (L_nonneg n) _) (term_pos n y).le)]
      exact mul_le_mul_of_nonneg_left (term_le_of_le n (le_of_lt hy)) (pow_nonneg (L_nonneg n) _))
    haβ ((summable_Lpow_term k hβ)) haβ
  rw [tsum_neg] at h
  exact h

theorem hasDerivAt_Z {β : ℝ} (hβ : 1 < β) : HasDerivAt Z (-M1 β) β := by
  have h := hasDerivAt_sum 0 hβ
  simp only [pow_zero, one_mul, zero_add, pow_one] at h
  exact h

theorem hasDerivAt_M1 {β : ℝ} (hβ : 1 < β) : HasDerivAt M1 (-M2 β) β := by
  have h := hasDerivAt_sum 1 hβ
  simp only [pow_one] at h
  exact h

theorem Z_pos {β : ℝ} (hβ : 1 < β) : 0 < Z β := by
  unfold Z
  exact (summable_Lpow_term 0 hβ |>.congr fun n => by simp).tsum_pos
    (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _)

/-- **`(log Z)'' = (Z M₂ − M₁²)/Z²`**: the derivative of the log-derivative `−M₁/Z`. -/
theorem hasDerivAt_logderiv {β : ℝ} (hβ : 1 < β) :
    HasDerivAt (fun y => -M1 y / Z y) ((Z β * M2 β - M1 β ^ 2) / Z β ^ 2) β := by
  have h := ((hasDerivAt_M1 hβ).neg).div (hasDerivAt_Z hβ) (Z_pos hβ).ne'
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply]
  field_simp

/-- **Strict positivity of the Fisher metric**: `M₁² < Z M₂` for `β > 1`. -/
theorem fisher_pos {β : ℝ} (hβ : 1 < β) : M1 β ^ 2 < Z β * M2 β := by
  -- Cauchy–Schwarz: (Σ √t · L√t)² ≤ (Σ t)(Σ L² t), with equality iff L is constant on the support.
  set c := M1 β / Z β with hc
  have hZ := Z_pos hβ
  have hs0 := summable_Lpow_term 0 hβ
  have hs1 := summable_Lpow_term 1 hβ
  have hs2 := summable_Lpow_term 2 hβ
  simp only [pow_zero, one_mul, pow_one] at hs0 hs1
  -- Σ (L − c)² term = M₂ − 2c M₁ + c² Z = M₂ − M₁²/Z, and it is > 0.
  have hexpand : ∑' n, (L n - c) ^ 2 * term n β = M2 β - 2 * c * M1 β + c ^ 2 * Z β := by
    have e : (fun n => (L n - c) ^ 2 * term n β) =
        fun n => L n ^ 2 * term n β - 2 * c * (L n * term n β) + c ^ 2 * term n β := by
      funext n; ring
    rw [e, Summable.tsum_add ((hs2.sub (hs1.mul_left (2 * c)))) (hs0.mul_left _),
      Summable.tsum_sub hs2 (hs1.mul_left _), tsum_mul_left, tsum_mul_left]
    rfl
  have hpos : 0 < ∑' n, (L n - c) ^ 2 * term n β := by
    have hsum : Summable fun n => (L n - c) ^ 2 * term n β := by
      have e : (fun n => (L n - c) ^ 2 * term n β) =
          fun n => L n ^ 2 * term n β - 2 * c * (L n * term n β) + c ^ 2 * term n β := by
        funext n; ring
      rw [e]; exact (hs2.sub (hs1.mul_left _)).add (hs0.mul_left _)
    -- L 0 = 0 and L 1 = log 2 > 0 differ, so (L n − c)² > 0 for n = 0 or n = 1
    by_cases h0 : c = 0
    · refine hsum.tsum_pos (fun n => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) 1 ?_
      apply mul_pos _ (Real.exp_pos _)
      rw [h0, sub_zero]
      have : 0 < L 1 := by unfold L; norm_num; exact Real.log_pos (by norm_num)
      positivity
    · refine hsum.tsum_pos (fun n => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) 0 ?_
      apply mul_pos _ (Real.exp_pos _)
      have hL0 : L 0 = 0 := by simp [L]
      rw [hL0, zero_sub]
      have : -c ≠ 0 := neg_ne_zero.mpr h0
      positivity
  rw [hexpand, hc] at hpos
  have : M2 β - 2 * (M1 β / Z β) * M1 β + (M1 β / Z β) ^ 2 * Z β = M2 β - M1 β ^ 2 / Z β := by
    field_simp; ring
  rw [this, sub_pos, div_lt_iff₀ hZ] at hpos
  linarith

end GppZetaFisherMetric
