import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The prime heat term is circular heat diffusion of the prime Poisson phase intensity

Source: Codex, GPPDiscovery2 `research/2026-09-27_rh_prime_heat_as_tfd_phase_diffusion.md`, §§1, 2, 5.

For absolutely summable coefficients `a, b`, define the even cosine series
`A(θ) = 1 + 2 Σ_{m≥1} a_m cos(mθ)` and similarly `B`. This file proves the circle pairing
* `pairing`: `(1/2π) ∫₀^{2π} A(θ) B(θ) dθ = 1 + 2 Σ_{m≥1} a_m b_m`.

Both the Poisson kernel `P_r` (`a_m = rᵐ`, `|r| < 1`) and the circle heat kernel `H_τ`
(`b_m = e^{−m²τ}`, `τ > 0`) are of this form, and both are even. So the normalized convolution
at the origin `(P_r * H_τ)(0) = (1/2π)∫ P_r(θ) H_τ(−θ) dθ` equals `(1/2π)∫ P_r H_τ`. That gives:
* `poisson_heat_pairing`: `(P_r * H_τ)(0) = 1 + 2 Σ_{m≥1} rᵐ e^{−m²τ}` (the note's §1 box).
* `prime_heat_term`: with `r = p^{−1/2}`, `L = log p`, `τ = L²/(4t)`, the prime heat contribution
  `B_p(t) = Σ_{m≥1} L rᵐ exp(−m²L²/(4t))` equals `(L/2)[(P_r * H_τ)(0) − 1]` (the §2 box).
* `prime_heat_term_pos`: `B_p(t) > 0` (the §5 local positivity).

**Not formalized:** the Brownian reading (§3), the Archimedean term and the global domination
`B_∞ ≥ B_prime` (§5). That domination is the open RH-equivalent problem, as the note says.
**No RH claim.**
-/

namespace GppPrimeHeatPhaseDiffusion

open Real intervalIntegral

theorem integral_cos_int {k : ℤ} (hk : k ≠ 0) : ∫ θ in (0 : ℝ)..2 * π, Real.cos (k * θ) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hk', integral_cos]
  have : (k : ℝ) * (2 * π) = ((2 * k : ℤ) : ℝ) * π := by push_cast; ring
  rw [this, Real.sin_int_mul_pi]; simp

theorem integral_cos_succ (m : ℕ) : ∫ θ in (0 : ℝ)..2 * π, Real.cos ((m + 1) * θ) = 0 := by
  have := integral_cos_int (k := (m + 1 : ℤ)) (by omega)
  push_cast at this; exact this

theorem cos_mul_cos (x y : ℝ) : Real.cos x * Real.cos y = (Real.cos (x - y) + Real.cos (x + y)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- Orthogonality of the cosine modes on `[0, 2π]`. -/
theorem orth (m n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, Real.cos ((m + 1) * θ) * Real.cos ((n + 1) * θ) =
      if m = n then π else 0 := by
  simp_rw [cos_mul_cos]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have hsum : ∀ θ : ℝ, ((m : ℝ) + 1) * θ + ((n : ℝ) + 1) * θ = (((m + n + 2 : ℤ)) : ℝ) * θ := by
    intro θ; push_cast; ring
  simp_rw [hsum]
  rw [integral_cos_int (by omega)]
  have hdiff : ∀ θ : ℝ, ((m : ℝ) + 1) * θ - ((n : ℝ) + 1) * θ = (((m : ℤ) - n : ℤ) : ℝ) * θ := by
    intro θ; push_cast; ring
  simp_rw [hdiff]
  split_ifs with h
  · subst h; simp
  · rw [integral_cos_int (by omega)]; simp

/-- Termwise integration of an absolutely summable series of uniformly bounded continuous functions. -/
theorem integral_tsum_mul (c : ℕ → ℝ) (hc : Summable fun m => |c m|) (u : ℕ → ℝ → ℝ)
    (hu : ∀ m, Continuous (u m)) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m θ, |u m θ| ≤ K) :
    ∫ θ in (0 : ℝ)..2 * π, ∑' m, c m * u m θ = ∑' m, c m * ∫ θ in (0 : ℝ)..2 * π, u m θ := by
  let f : ℕ → C(ℝ, ℝ) := fun m => ⟨fun θ => c m * u m θ, (hu m).const_mul _⟩
  have hnorm : ∀ m, ‖(f m).restrict (⟨Set.uIcc 0 (2 * π), isCompact_uIcc⟩ :
      TopologicalSpace.Compacts ℝ)‖ ≤ |c m| * K := by
    intro m
    refine (ContinuousMap.norm_le _ (by positivity)).mpr fun x => ?_
    simp only [ContinuousMap.restrict_apply, ContinuousMap.coe_mk, f, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hK m x) (abs_nonneg _)
  have hs := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm (a := 0) (b := 2 * π)
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm (hc.mul_right K))
  simp only [f, ContinuousMap.coe_mk] at hs
  rw [← hs]
  congr 1; ext m
  exact intervalIntegral.integral_const_mul _ _

/-- The even cosine series `1 + 2 Σ_{m≥1} a_m cos(mθ)` (with `a m` the coefficient of mode `m+1`). -/
noncomputable def cosSeries (a : ℕ → ℝ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑' m, a m * Real.cos ((m + 1) * θ)

theorem summable_cos_terms {a : ℕ → ℝ} (ha : Summable fun m => |a m|) (θ : ℝ) :
    Summable fun m => a m * Real.cos ((m + 1) * θ) :=
  Summable.of_norm_bounded ha fun m => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem continuous_cosSeries {a : ℕ → ℝ} (ha : Summable fun m => |a m|) :
    Continuous (cosSeries a) := by
  unfold cosSeries
  refine continuous_const.add (continuous_const.mul ?_)
  refine continuous_tsum (fun m => by fun_prop) ha fun m θ => ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem abs_cosSeries_le {a : ℕ → ℝ} (ha : Summable fun m => |a m|) (θ : ℝ) :
    |cosSeries a θ| ≤ 1 + 2 * ∑' m, |a m| := by
  unfold cosSeries
  have h1 : |∑' m, a m * Real.cos ((m + 1) * θ)| ≤ ∑' m, |a m| := by
    calc |∑' m, a m * Real.cos ((m + 1) * θ)| ≤ ∑' m, |a m * Real.cos ((m + 1) * θ)| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm (summable_cos_terms ha θ).norm
      _ ≤ ∑' m, |a m| := by
          refine Summable.tsum_le_tsum (fun m => ?_) (summable_cos_terms ha θ).abs ha
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  calc |1 + 2 * ∑' m, a m * Real.cos ((m + 1) * θ)|
      ≤ |(1 : ℝ)| + |2 * ∑' m, a m * Real.cos ((m + 1) * θ)| := abs_add_le _ _
    _ ≤ 1 + 2 * ∑' m, |a m| := by rw [abs_one, abs_mul, abs_two]; linarith

theorem integral_cosSeries_mul_cos {a : ℕ → ℝ} (ha : Summable fun m => |a m|) (n : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π, cosSeries a θ * Real.cos ((n + 1) * θ) = 2 * π * a n := by
  have hexp : ∀ θ, cosSeries a θ * Real.cos ((n + 1) * θ) = Real.cos ((n + 1) * θ) +
      ∑' m, (2 * a m) * (Real.cos ((m + 1) * θ) * Real.cos ((n + 1) * θ)) := by
    intro θ
    unfold cosSeries
    rw [add_mul, one_mul, mul_assoc, ← tsum_mul_right, ← tsum_mul_left]
    congr 2; funext m; ring
  have hb1 : ∀ (m : ℕ) (θ : ℝ), |Real.cos ((m + 1) * θ) * Real.cos ((n + 1) * θ)| ≤ 1 := by
    intro m θ
    rw [abs_mul]
    exact mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_cos_le_one _)
  have hcont : Continuous fun θ : ℝ =>
      ∑' m, (2 * a m) * (Real.cos ((m + 1) * θ) * Real.cos ((n + 1) * θ)) := by
    have h := ((continuous_cosSeries ha).mul (by fun_prop : Continuous fun θ : ℝ =>
      Real.cos ((n + 1) * θ))).sub (by fun_prop : Continuous fun θ : ℝ => Real.cos ((n + 1) * θ))
    refine h.congr fun θ => ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [hexp]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
    (hcont.intervalIntegrable _ _)]
  rw [integral_cos_succ, zero_add, integral_tsum_mul (fun m => 2 * a m)
    (by simpa [abs_mul] using ha.mul_left 2) _ (fun m => by fun_prop) 1 zero_le_one hb1]
  simp_rw [orth, mul_ite, mul_zero]
  rw [tsum_ite_eq]; ring

theorem integral_cosSeries {a : ℕ → ℝ} (ha : Summable fun m => |a m|) :
    ∫ θ in (0 : ℝ)..2 * π, cosSeries a θ = 2 * π := by
  unfold cosSeries
  rw [intervalIntegral.integral_add intervalIntegrable_const ?_, intervalIntegral.integral_const_mul,
    integral_tsum_mul a ha _ (fun m => by fun_prop) 1 zero_le_one
      (fun m θ => Real.abs_cos_le_one _)]
  · simp [integral_cos_succ]
  · exact Continuous.intervalIntegrable (continuous_const.mul (continuous_tsum
      (fun m => by fun_prop) ha fun m θ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))) _ _

/-- **Circle pairing**: `(1/2π)∫₀^{2π} A B = 1 + 2 Σ a_m b_m`. -/
theorem pairing {a b : ℕ → ℝ} (ha : Summable fun m => |a m|) (hb : Summable fun m => |b m|) :
    (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π, cosSeries a θ * cosSeries b θ =
      1 + 2 * ∑' m, a m * b m := by
  set C := 1 + 2 * ∑' m, |a m| with hC
  have hC0 : 0 ≤ C := by
    have : 0 ≤ ∑' m, |a m| := tsum_nonneg fun m => abs_nonneg (a m)
    rw [hC]; linarith
  have hexp : ∀ θ, cosSeries a θ * cosSeries b θ = cosSeries a θ +
      ∑' n, (2 * b n) * (cosSeries a θ * Real.cos ((n + 1) * θ)) := by
    intro θ
    show cosSeries a θ * (1 + 2 * ∑' n, b n * Real.cos ((n + 1) * θ)) = _
    rw [mul_add, mul_one, ← tsum_mul_left, ← tsum_mul_left]
    congr 2; funext n; ring
  have hcA := continuous_cosSeries ha
  have hbound : ∀ (n : ℕ) (θ : ℝ), |cosSeries a θ * Real.cos ((n + 1) * θ)| ≤ C := by
    intro n θ
    rw [abs_mul]
    calc |cosSeries a θ| * |Real.cos ((n + 1) * θ)| ≤ |cosSeries a θ| * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
      _ ≤ C := by rw [mul_one]; exact abs_cosSeries_le ha θ
  have hcont : Continuous fun θ : ℝ =>
      ∑' n, (2 * b n) * (cosSeries a θ * Real.cos ((n + 1) * θ)) := by
    refine ((hcA.mul (continuous_cosSeries hb)).sub hcA).congr fun θ => ?_
    simp only [Pi.mul_apply, Pi.sub_apply]
    rw [hexp]; ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (hcA.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  rw [integral_cosSeries ha, integral_tsum_mul (fun n => 2 * b n)
    (by simpa [abs_mul] using hb.mul_left 2) _ (fun n => by fun_prop) C hC0 hbound]
  simp_rw [integral_cosSeries_mul_cos ha]
  have hpi : (2 * π) ≠ 0 := by positivity
  have hsab : ∑' n, 2 * b n * (2 * π * a n) = (2 * π) * (2 * ∑' n, a n * b n) := by
    rw [← tsum_mul_left, ← tsum_mul_left]; congr 1; funext n; ring
  rw [hsab]; field_simp

theorem summable_abs_geom {r : ℝ} (hr : |r| < 1) : Summable fun m : ℕ => |r ^ (m + 1)| := by
  simp_rw [abs_pow, pow_succ]
  exact (summable_geometric_of_lt_one (abs_nonneg r) hr).mul_right _

theorem summable_abs_heat {τ : ℝ} (hτ : 0 < τ) :
    Summable fun m : ℕ => |Real.exp (-(((m : ℝ) + 1) ^ 2 * τ))| := by
  simp_rw [abs_of_pos (Real.exp_pos _)]
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_geometric_of_lt_one (Real.exp_pos (-τ)).le
      (Real.exp_zero ▸ Real.exp_lt_exp.mpr (by linarith : -τ < 0))).mul_right (Real.exp (-τ)))
  rw [← pow_succ, ← Real.exp_nat_mul, Real.exp_le_exp]
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  push_cast
  nlinarith [mul_nonneg (mul_nonneg hm (by linarith : (0 : ℝ) ≤ m + 1)) hτ.le]

/-- **Poisson ∗ heat at the origin**: `(P_r * H_τ)(0) = 1 + 2 Σ_{m≥1} rᵐ e^{−m²τ}`. -/
theorem poisson_heat_pairing {r τ : ℝ} (hr : |r| < 1) (hτ : 0 < τ) :
    (1 / (2 * π)) * ∫ θ in (0 : ℝ)..2 * π,
        cosSeries (fun m => r ^ (m + 1)) θ * cosSeries (fun m => Real.exp (-((m + 1) ^ 2 * τ))) θ =
      1 + 2 * ∑' m : ℕ, r ^ (m + 1) * Real.exp (-((m + 1) ^ 2 * τ)) :=
  pairing (summable_abs_geom hr) (summable_abs_heat hτ)

/-- **The prime heat term is diffusion of phase intensity**:
`Σ_{m≥1} L rᵐ e^{−m²L²/(4t)} = (L/2)[(P_r * H_{L²/(4t)})(0) − 1]`. -/
theorem prime_heat_term {r L t : ℝ} (hr : |r| < 1) (hL : L ≠ 0) (ht : 0 < t) :
    ∑' m : ℕ, L * r ^ (m + 1) * Real.exp (-(((m : ℝ) + 1) ^ 2 * L ^ 2 / (4 * t))) =
      L / 2 * ((1 / (2 * π)) * (∫ θ in (0 : ℝ)..2 * π,
        cosSeries (fun m => r ^ (m + 1)) θ *
          cosSeries (fun m => Real.exp (-((m + 1) ^ 2 * (L ^ 2 / (4 * t))))) θ) - 1) := by
  rw [poisson_heat_pairing hr (by positivity)]
  rw [add_sub_cancel_left, ← mul_assoc, show L / 2 * 2 = L by ring, ← tsum_mul_left]
  congr 1; funext m; rw [mul_div_assoc]; ring

/-- **Local positivity**: for `0 < r < 1`, `L > 0`, `t > 0` the prime heat term is positive. -/
theorem prime_heat_term_pos {r L t : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hL : 0 < L) (ht : 0 < t) :
    0 < ∑' m : ℕ, L * r ^ (m + 1) * Real.exp (-(((m : ℝ) + 1) ^ 2 * L ^ 2 / (4 * t))) := by
  have hs : Summable fun m : ℕ => L * r ^ (m + 1) * Real.exp (-(((m : ℝ) + 1) ^ 2 * L ^ 2 / (4 * t))) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      ((summable_abs_geom (by rw [abs_of_pos hr0]; exact hr1)).mul_left L)
    rw [abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr (by
      rw [neg_nonpos]; positivity))
  exact hs.tsum_pos (fun m => by positivity) 0 (by positivity)

end GppPrimeHeatPhaseDiffusion
