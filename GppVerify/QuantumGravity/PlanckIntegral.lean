import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# The Planck integral: `∫₀^∞ x³/(eˣ−1) dx = π⁴/15`

Thread P of `docs/FORMALIZATION_PLAN.md`, from `blackbody_law_qg_v1.tex` (the
Stefan–Boltzmann quartic — the exact constant behind the blackbody radiation law, which
the paper recasts as the Gibbs weight of the celestial boost).

The classical proof, executed in full: expand `1/(eˣ−1)` as the geometric series
`Σ_{n≥0} e^{−(n+1)x}` (valid pointwise for `x > 0`), interchange sum and integral
(`integral_tsum_of_summable_integral_norm` — the norms sum to `Σ 6/(n+1)⁴ < ∞`), evaluate
each term by the Gamma integral (`∫₀^∞ x³e^{−(n+1)x} dx = Γ(4)/(n+1)⁴ = 6/(n+1)⁴`), and
sum with `ζ(4) = π⁴/90` (`hasSum_zeta_four`): `6·π⁴/90 = π⁴/15`.

Every analytic ingredient is genuine: the interchange is justified by summability, the
term integrals by the pinned Mathlib's `integral_rpow_mul_exp_neg_mul_rpow`, and the zeta
value by Mathlib's Bernoulli machinery — no step is assumed.
-/

namespace GppPlanck

open MeasureTheory Real Set

/-- The term integral: `∫₀^∞ x³ e^{−(n+1)x} dx = 6/(n+1)⁴` (`Γ(4) = 3! = 6`). -/
theorem integral_pow_three_mul_exp (n : ℕ) :
    ∫ x in Ioi (0:ℝ), x ^ 3 * Real.exp (-((n:ℝ) + 1) * x) = 6 / ((n:ℝ) + 1) ^ 4 := by
  have hb : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 3) (b := (n:ℝ) + 1)
    one_pos (by norm_num) hb
  -- clean the exponents and the Gamma argument
  rw [show (-(3 + 1) / 1 : ℝ) = -((4:ℕ) : ℝ) by norm_num,
      show ((3 + 1) / 1 : ℝ) = 4 by norm_num] at key
  have hg : Real.Gamma 4 = 6 := by
    have h := Real.Gamma_nat_eq_factorial 3
    norm_num at h
    exact h
  rw [hg, Real.rpow_neg hb.le, Real.rpow_natCast] at key
  simp_rw [Real.rpow_one] at key
  -- bridge the statement's npow to the lemma's rpow
  have hpow3 : ∀ x : ℝ, x ^ (3:ℕ) = x ^ (3:ℝ) := fun x => by
    rw [show (3:ℝ) = ((3:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simp_rw [hpow3]
  rw [key]
  ring

/-- Each term is integrable on `(0,∞)`: dominated by the Euler Gamma integrand at `s=4`,
    since `e^{−(n+1)x} ≤ e^{−x}` for `x ≥ 0`. -/
theorem integrable_term (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ 3 * Real.exp (-((n:ℝ) + 1) * x)) (Ioi (0:ℝ)) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((4:ℝ) - 1)) (Ioi (0:ℝ)) :=
    Real.GammaIntegral_convergent (by norm_num : (0:ℝ) < 4)
  refine hg.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    exact (continuous_pow 3).mul
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)))
  · rw [ae_restrict_iff' measurableSet_Ioi]
    apply Filter.Eventually.of_forall
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have hbound : Real.exp (-((n:ℝ) + 1) * x) ≤ Real.exp (-x) := by
      apply Real.exp_le_exp.mpr
      have : (1:ℝ) ≤ (n:ℝ) + 1 := by positivity
      nlinarith
    have hpow : x ^ ((4:ℝ) - 1) = x ^ (3:ℕ) := by
      rw [show (4:ℝ) - 1 = ((3:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hpow]
    calc x ^ 3 * Real.exp (-((n:ℝ) + 1) * x) ≤ x ^ 3 * Real.exp (-x) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Real.exp (-x) * x ^ 3 := by ring

/-- The summed values: `Σ_{n≥0} 6/(n+1)⁴ = 6·ζ(4) = π⁴/15`. -/
theorem hasSum_six_div_pow_four :
    HasSum (fun n : ℕ => 6 / ((n:ℝ) + 1) ^ 4) (π ^ 4 / 15) := by
  have h := hasSum_zeta_four
  have h1 : HasSum (fun n : ℕ => 1 / (((n:ℝ) + 1) ^ 4)) (π ^ 4 / 90) := by
    have h2 := (hasSum_nat_add_iff (f := fun n : ℕ => 1 / ((n:ℝ)) ^ 4) 1).mpr
      (by simpa using h)
    simpa [Nat.cast_add, Nat.cast_one] using h2
  have h6 := h1.mul_left 6
  have hfun : (fun n : ℕ => 6 * (1 / ((n:ℝ) + 1) ^ 4)) =
      fun n : ℕ => 6 / ((n:ℝ) + 1) ^ 4 := by
    funext n
    ring
  rw [hfun] at h6
  rw [show 6 * (π ^ 4 / 90) = π ^ 4 / 15 by ring] at h6
  exact h6

/-- The pointwise geometric expansion, for `x > 0`:
    `x³/(eˣ−1) = Σ_{n≥0} x³·e^{−(n+1)x}`. -/
theorem planck_summand_eq {x : ℝ} (hx : 0 < x) :
    x ^ 3 / (Real.exp x - 1) = ∑' n : ℕ, x ^ 3 * Real.exp (-((n:ℝ) + 1) * x) := by
  have hlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : (0:ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hterm : ∀ n : ℕ, x ^ 3 * Real.exp (-((n:ℝ) + 1) * x) =
      (x ^ 3 * Real.exp (-x)) * (Real.exp (-x)) ^ n := by
    intro n
    rw [show -((n:ℝ) + 1) * x = (n:ℝ) * (-x) + (-x) by ring, Real.exp_add,
      Real.exp_nat_mul]
    ring
  rw [tsum_congr hterm, tsum_mul_left, tsum_geometric_of_lt_one h0 hlt]
  have hgt : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have hne : Real.exp x - 1 ≠ 0 := by linarith
  have hne2 : 1 - Real.exp (-x) ≠ 0 := by linarith
  have hexpne : Real.exp x ≠ 0 := Real.exp_ne_zero x
  rw [Real.exp_neg]
  field_simp
  ring

/-- **The Planck integral**: `∫₀^∞ x³/(eˣ−1) dx = π⁴/15` — the Stefan–Boltzmann
    quartic, exactly. -/
theorem planck_integral :
    ∫ x in Ioi (0:ℝ), x ^ 3 / (Real.exp x - 1) = π ^ 4 / 15 := by
  have hnorm : ∀ n : ℕ, (∫ x in Ioi (0:ℝ), ‖x ^ 3 * Real.exp (-((n:ℝ) + 1) * x)‖) =
      6 / ((n:ℝ) + 1) ^ 4 := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun x : ℝ =>
        x ^ 3 * Real.exp (-((n:ℝ) + 1) * x)) (fun x hx => by
      have hx' : (0:ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])]
    exact integral_pow_three_mul_exp n
  have hsum : Summable (fun n : ℕ =>
      ∫ x in Ioi (0:ℝ), ‖x ^ 3 * Real.exp (-((n:ℝ) + 1) * x)‖) := by
    apply Summable.congr hasSum_six_div_pow_four.summable
    intro n
    exact (hnorm n).symm
  have hswap := integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => fun x : ℝ => x ^ 3 * Real.exp (-((n:ℝ) + 1) * x))
    (μ := (volume : Measure ℝ).restrict (Ioi 0)) integrable_term hsum
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => planck_summand_eq (show (0:ℝ) < x from hx)), ← hswap,
    tsum_congr (fun n => integral_pow_three_mul_exp n)]
  exact hasSum_six_div_pow_four.tsum_eq

end GppPlanck
