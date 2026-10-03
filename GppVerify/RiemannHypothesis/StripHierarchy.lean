import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Regularized prime scattering products and the Schatten strip hierarchy

Source: Codex, GPPDiscovery2 `research/2026-09-27_regularized_prime_scattering_strip_hierarchy.md`,
§§2–4.

Remove the first `k − 1` repetition harmonics of the prime Blaschke phase, so the local log-phase
is `2i Σ_{m ≥ k} (a_p^m / m) sin(m T log p)` with `a_p = p^{-1/2}` and `T = x + iy`.

* `norm_sin_le`: `|sin w| ≤ e^{|Im w|}`, so the `m`-th term is bounded by `p^{-m(1/2 − |y|)}`
  (`weight_eq`);
* `prime_tail_summable`: if `σ = 1/2 − |y| > 0` and `kσ > 1`, the majorant
  `Σ_p Σ_{m ≥ k} p^{-mσ}` is finite, so the logarithm of the product `Π_p B̃_{p,≥k}(T)` converges
  normally (absolute and locally uniform in `x`) in that strip;
* `leading_summable_iff`: the worst repetition `m = k` is summable over the primes iff `kσ > 1`,
  so the condition is sharp for this majorant;
* `strip_iff`: `kσ > 1 ⟺ |y| < 1/2 − 1/k`, the centered form of the Schatten condition
  `k Re s > 1` (`s = 1/2 + iT`, `Re s = 1/2 − Im T`); for `k = 3` it is `|Im T| < 1/6`
  (`strip_three`).

## Checks and scope

All claims check. **Not formalized:** the identification of the regularized factor with the product
`Π_p B̃_{p,≥k}` as an analytic function (the exponential counterterm and the branch of the
logarithm), the unit modulus on the real axis, and the identification of its real-axis phase
derivative with the `m ≥ 3` part of the half-density von Mangoldt current. No RH claim.
-/

open Real Complex

namespace GppStripHierarchy

/-- `|sin w| ≤ e^{|Im w|}`. -/
theorem norm_sin_le (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  rw [Complex.sin]
  have h1 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [le_abs_self]
  have h2 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [neg_le_abs]
  calc ‖(Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) * Complex.I / 2‖
      = ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2 := by
        rw [norm_div, norm_mul, Complex.norm_I, mul_one]; simp
    _ ≤ (‖Complex.exp (-w * Complex.I)‖ + ‖Complex.exp (w * Complex.I)‖) / 2 := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by gcongr
    _ = Real.exp |w.im| := by ring

/-- `p^{-m/2} · e^{m (log p) |y|} = p^{-m (1/2 − |y|)}`. -/
theorem weight_eq (p : ℝ) (hp : 0 < p) (m : ℕ) (y : ℝ) :
    (p ^ (-(1 / 2 : ℝ))) ^ m * Real.exp ((m : ℝ) * Real.log p * |y|) =
      p ^ (-((m : ℝ) * (1 / 2 - |y|))) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le, Real.rpow_def_of_pos hp,
    Real.rpow_def_of_pos hp, ← Real.exp_add]
  congr 1
  ring

/-- **Normal convergence in the strip.** -/
theorem prime_tail_summable (k : ℕ) (σ : ℝ) (hσ : 0 < σ) (hk : 1 < (k : ℝ) * σ) :
    Summable (fun p : Nat.Primes => ∑' m : ℕ, (p : ℝ) ^ (-(((m + k : ℕ) : ℝ) * σ))) := by
  have hq0 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hq0pos : 0 < (2 : ℝ) ^ (-σ) := Real.rpow_pos_of_pos (by norm_num) _
  have hs : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-((k : ℝ) * σ))) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun m => by positivity) (fun p => ?_)
    (hs.mul_left (1 / (1 - (2 : ℝ) ^ (-σ))))
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set q : ℝ := (p : ℝ) ^ (-σ) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos hp0 _
  have hqle : q ≤ (2 : ℝ) ^ (-σ) := by
    rw [hq]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
  have hq1 : q < 1 := lt_of_le_of_lt hqle hq0
  have hterm : ∀ m : ℕ, (p : ℝ) ^ (-(((m + k : ℕ) : ℝ) * σ)) = q ^ k * q ^ m := by
    intro m
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
      ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hqpos.le hq1]
  have hqk : q ^ k = (p : ℝ) ^ (-((k : ℝ) * σ)) := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1; ring
  rw [hqk]
  have h1 : (1 - q)⁻¹ ≤ 1 / (1 - (2 : ℝ) ^ (-σ)) := by
    rw [one_div]
    exact inv_anti₀ (by linarith) (by linarith)
  calc (p : ℝ) ^ (-((k : ℝ) * σ)) * (1 - q)⁻¹
      ≤ (p : ℝ) ^ (-((k : ℝ) * σ)) * (1 / (1 - (2 : ℝ) ^ (-σ))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 1 / (1 - (2 : ℝ) ^ (-σ)) * (p : ℝ) ^ (-((k : ℝ) * σ)) := by ring

/-- **Sharpness for the leading term.** The `m = k` majorant is summable over primes iff `kσ > 1`. -/
theorem leading_summable_iff (k : ℕ) (σ : ℝ) :
    Summable (fun p : Nat.Primes => (p : ℝ) ^ (-((k : ℝ) * σ))) ↔ 1 < (k : ℝ) * σ := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **The strip.** `kσ > 1 ⟺ |y| < 1/2 − 1/k` for `σ = 1/2 − |y|`. -/
theorem strip_iff (k : ℕ) (hk : 0 < k) (y : ℝ) :
    1 < (k : ℝ) * (1 / 2 - |y|) ↔ |y| < 1 / 2 - 1 / (k : ℝ) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', one_div, lt_sub_comm]
  constructor
  · intro h
    have : 1 / (k : ℝ) < 1 / 2 - |y| := by
      rw [div_lt_iff₀ hk']; linarith
    linarith
  · intro h
    have : 1 / (k : ℝ) < 1 / 2 - |y| := by linarith
    rw [div_lt_iff₀ hk'] at this
    linarith

/-- **The `det₃` strip.** For `k = 3`, the strip is `|Im T| < 1/6`. -/
theorem strip_three (y : ℝ) : 1 < (3 : ℝ) * (1 / 2 - |y|) ↔ |y| < 1 / 6 := by
  constructor <;> intro h <;> linarith

end GppStripHierarchy
