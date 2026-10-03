import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The exact totient response: Möbius form, the smoothing kernel `G`, and divisor regrouping

Source: Codex, bridge `research/codex/2026-10-03_totient_volterra_cancellation.md`, §§2–4, 6
(exact elementary parts; the estimate `TARGET` of §5, the Bessel transform and the adversarial
control of §§6–7 are not formalized).

* `totient_div` (§4): `φ(n)/n = Σ_{d ∣ n} μ(d)/d`;
* `G`, `G_zero`, `G_one` (§2): the continuous kernel `G(y) = 4 y arccos y − 2 √(1−y²)` has
  `G(0) = −2` and `G(1) = 0`;
* `hasDerivAt_G` (§4): `G'(y) = 4 arccos y − 2y/√(1−y²)` on `(0,1)`;
* `integral_G` (§4): the exact zero mean `∫₀¹ G(y) dy = 0`, from `∫ y arccos y = π/8` and
  `∫ √(1−y²) = π/4`;
* `hasDerivAt_g` and `tendsto_g_zero` (§2): with `a(v) = (2e^{-v} − 1)/√(1 − e^{-v})` and
  `g(v) = G(e^{-v/2})`, `g' = a − g/2` on `v > 0` and `g(v) → 0` as `v ↓ 0`; this is the
  differential form of the second causal filter, `g = ∫₀^v e^{-(v−u)/2} a(u) du`;
* `sum_regroup` (§6): for `x ≥ 1`, `Σ_{n ≤ x} (φ(n)/n) G(n/x) = Σ_{d ≤ x} (μ(d)/d) A_G(x/d)` with
  `A_G(y) = Σ_{1 ≤ k ≤ y} G(k/y)`.

## Checks and scope

All of these check. Two precision points: the note&rsquo;s statement
`g(v) = ∫₀^v e^{-(v−u)/2} a(u) du` is formalized in its equivalent ODE-plus-initial-value form
(the integral itself is singular at `0` like `u^{-1/2}`), and the unconditional bound
`K(x) = O(log(2+x))` and the identification of the Laplace transform with `S(s)/(s + 1/2)` are not
formalized. No RH claim.
-/

open Real Finset ArithmeticFunction MeasureTheory
open scoped ArithmeticFunction.Moebius

namespace GppTotientVolterra

/-! ### The Möbius form of `φ(n)/n` -/

/-- **`φ(n)/n = Σ_{d ∣ n} μ(d)/d`.** -/
theorem totient_div (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℝ) / n = ∑ d ∈ n.divisors, (μ d : ℝ) / d := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun m => (Nat.totient m : ℝ)) (g := fun m => (m : ℝ))).mp
    (fun m hm => by exact_mod_cast Nat.sum_totient m) n hn
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℝ) * (b : ℝ))] at key
  rw [← key, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / d := Nat.cast_div hdn (by exact_mod_cast hd0.ne')
  rw [hcast]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
  field_simp

/-! ### The kernel `G` -/

/-- The smoothing kernel `G(y) = 4 y arccos y − 2 √(1 − y²)`. -/
noncomputable def G (y : ℝ) : ℝ := 4 * y * Real.arccos y - 2 * Real.sqrt (1 - y ^ 2)

@[simp] theorem G_zero : G 0 = -2 := by simp [G, Real.arccos_zero]

@[simp] theorem G_one : G 1 = 0 := by simp [G]

theorem continuous_G : Continuous G := by
  unfold G
  fun_prop

theorem hasDerivAt_G (y : ℝ) (h0 : 0 < y) (h1 : y < 1) :
    HasDerivAt G (4 * Real.arccos y - 2 * y / Real.sqrt (1 - y ^ 2)) y := by
  have hs : 0 < 1 - y ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hacos := Real.hasDerivAt_arccos (x := y) (by linarith) h1.ne
  have hroot : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_sub 1)
  have hsqrt := hroot.sqrt hs.ne'
  have h := (((hasDerivAt_id y).const_mul 4).mul hacos).sub (hsqrt.const_mul 2)
  unfold G
  refine HasDerivAt.congr_deriv (f := fun z : ℝ => 4 * z * Real.arccos z - 2 * Real.sqrt (1 - z ^ 2)) h ?_
  simp only [id]
  field_simp
  ring

/-! ### The zero mean -/

/-- `F(y) = ((2y² − 1)/4) arccos y − y √(1 − y²)/4`, an antiderivative of `y arccos y`. -/
noncomputable def F (y : ℝ) : ℝ :=
  (2 * y ^ 2 - 1) / 4 * Real.arccos y - y * Real.sqrt (1 - y ^ 2) / 4

theorem continuous_F : Continuous F := by
  unfold F
  fun_prop

theorem hasDerivAt_F (y : ℝ) (h0 : 0 < y) (h1 : y < 1) :
    HasDerivAt F (y * Real.arccos y) y := by
  have hs : 0 < 1 - y ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq2 : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hs.le
  have hacos := Real.hasDerivAt_arccos (x := y) (by linarith) h1.ne
  have hroot : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * y)) y := by
    simpa using ((hasDerivAt_pow 2 y).const_sub 1)
  have hsqrt := hroot.sqrt hs.ne'
  have hp : HasDerivAt (fun y : ℝ => (2 * y ^ 2 - 1) / 4) y y := by
    have := (((hasDerivAt_pow 2 y).const_mul 2).sub_const 1).div_const 4
    refine HasDerivAt.congr_deriv this ?_
    ring
  have h := (hp.mul hacos).sub (((hasDerivAt_id y).mul hsqrt).div_const 4)
  unfold F
  refine HasDerivAt.congr_deriv (f := fun z : ℝ => (2 * z ^ 2 - 1) / 4 * Real.arccos z - z * Real.sqrt (1 - z ^ 2) / 4) h ?_
  simp only [id]
  field_simp
  nlinarith [hsq2]

theorem integral_y_arccos : ∫ y in (0 : ℝ)..1, y * Real.arccos y = Real.pi / 8 := by
  have hint : IntervalIntegrable (fun y : ℝ => y * Real.arccos y) volume 0 1 :=
    (by fun_prop : Continuous fun y : ℝ => y * Real.arccos y).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
    continuous_F.continuousOn
    (fun y hy => (hasDerivAt_F y hy.1 hy.2).hasDerivWithinAt) hint]
  simp [F, Real.arccos_zero]
  ring

theorem integral_sqrt_quarter : ∫ y in (0 : ℝ)..1, Real.sqrt (1 - y ^ 2) = Real.pi / 4 := by
  have hfull := integral_sqrt_one_sub_sq
  have hsplit : ∫ x in (-1 : ℝ)..1, Real.sqrt (1 - x ^ 2) =
      (∫ x in (-1 : ℝ)..0, Real.sqrt (1 - x ^ 2)) + ∫ x in (0 : ℝ)..1, Real.sqrt (1 - x ^ 2) :=
    (intervalIntegral.integral_add_adjacent_intervals
      ((by fun_prop : Continuous fun x : ℝ => Real.sqrt (1 - x ^ 2)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => Real.sqrt (1 - x ^ 2)).intervalIntegrable _ _)).symm
  have hneg : ∫ x in (-1 : ℝ)..0, Real.sqrt (1 - x ^ 2) = ∫ x in (0 : ℝ)..1, Real.sqrt (1 - x ^ 2) := by
    have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun x : ℝ => Real.sqrt (1 - x ^ 2))
    simp only [neg_sq, neg_zero] at this
    exact this.symm
  linarith

/-- **The exact zero mean**: `∫₀¹ G(y) dy = 0`. -/
theorem integral_G : ∫ y in (0 : ℝ)..1, G y = 0 := by
  have h1 : ∫ y in (0 : ℝ)..1, G y =
      4 * (∫ y in (0 : ℝ)..1, y * Real.arccos y) - 2 * ∫ y in (0 : ℝ)..1, Real.sqrt (1 - y ^ 2) := by
    unfold G
    have e : (fun y : ℝ => 4 * y * Real.arccos y) = fun y => 4 * (y * Real.arccos y) := by
      funext y; ring
    rw [intervalIntegral.integral_sub, e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    · exact (by fun_prop : Continuous fun y : ℝ => 4 * y * Real.arccos y).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun y : ℝ => 2 * Real.sqrt (1 - y ^ 2)).intervalIntegrable _ _
  rw [h1, integral_y_arccos, integral_sqrt_quarter]
  ring

/-! ### The second causal filter -/

/-- `a(v) = (2 e^{-v} − 1)/√(1 − e^{-v})`. -/
noncomputable def a (v : ℝ) : ℝ := (2 * Real.exp (-v) - 1) / Real.sqrt (1 - Real.exp (-v))

/-- `g(v) = G(e^{-v/2})`. -/
noncomputable def g (v : ℝ) : ℝ := G (Real.exp (-v / 2))

/-- **The ODE form of the filter**: `g' = a − g/2` for `v > 0`. -/
theorem hasDerivAt_g (v : ℝ) (hv : 0 < v) : HasDerivAt g (a v - g v / 2) v := by
  have hy0 : 0 < Real.exp (-v / 2) := Real.exp_pos _
  have hy1 : Real.exp (-v / 2) < 1 := by rw [Real.exp_lt_one_iff]; linarith
  set y := Real.exp (-v / 2) with hy
  have hyy : y ^ 2 = Real.exp (-v) := by
    rw [hy, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hs : 0 < 1 - y ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 - y ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have hsq2 : Real.sqrt (1 - y ^ 2) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hs.le
  have hyd : HasDerivAt (fun v : ℝ => Real.exp (-v / 2)) (-(y / 2)) v := by
    have := ((hasDerivAt_id v).neg.div_const 2).exp
    refine HasDerivAt.congr_deriv this ?_
    show Real.exp (-v / 2) * (-1 / 2) = -(y / 2)
    rw [← hy]; ring
  have hG := (hasDerivAt_G y hy0 hy1).comp v hyd
  refine HasDerivAt.congr_deriv (f := g) hG ?_
  unfold a g G
  rw [← hy, ← hyy]
  field_simp
  nlinarith [hsq2]

theorem tendsto_g_zero : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Filter.Tendsto g (nhds 0) (nhds (g 0)) := by
    have : Continuous g := by unfold g; exact continuous_G.comp (by fun_prop)
    exact this.tendsto 0
  have h0 : g 0 = 0 := by simp [g]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### Divisor regrouping -/

/-- `A_G(y) = Σ_{1 ≤ k ≤ y} G(k/y)`. -/
noncomputable def AG (y : ℝ) : ℝ := ∑ k ∈ Icc 1 ⌊y⌋₊, G ((k : ℝ) / y)

/-- The response `K(x) = Σ_{n ≤ x} (φ(n)/n) G(n/x)`. -/
noncomputable def K (x : ℝ) : ℝ := ∑ n ∈ Icc 1 ⌊x⌋₊, (Nat.totient n : ℝ) / n * G ((n : ℝ) / x)

/-- **Divisor regrouping**: `K(x) = Σ_{d ≤ x} (μ(d)/d) A_G(x/d)`. -/
theorem sum_regroup (x : ℝ) (hx : 0 < x) :
    K x = ∑ d ∈ Icc 1 ⌊x⌋₊, (μ d : ℝ) / d * AG (x / d) := by
  set N := ⌊x⌋₊ with hN
  have step1 : K x = ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (μ d : ℝ) / d * G ((n : ℝ) / x) := by
    unfold K
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.sum_mul, totient_div n (Finset.mem_Icc.mp hn).1]
  have step2 : ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, (μ d : ℝ) / d * G ((n : ℝ) / x) =
      ∑ d ∈ Icc 1 N, ∑ n ∈ (Icc 1 N).filter (d ∣ ·), (μ d : ℝ) / d * G ((n : ℝ) / x) := by
    refine Finset.sum_comm' ?_
    intro n d
    simp only [Finset.mem_Icc, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, _⟩
      have h5 := Nat.le_of_dvd (by omega) h3
      have h6 := Nat.pos_of_dvd_of_pos h3 (by omega)
      exact ⟨⟨⟨h1, h2⟩, h3⟩, by omega, by omega⟩
    · intro h
      exact ⟨h.1.1, h.1.2, by omega⟩
  rw [step1, step2]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  unfold AG
  rw [Nat.floor_div_natCast x d, ← hN, ← Finset.mul_sum]
  congr 1
  refine Finset.sum_nbij' (fun n => n / d) (fun k => d * k) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left _ (by omega)]
    have hd0 : 0 < d := by omega
    refine ⟨?_, (Nat.le_div_iff_mul_le hd0).mpr (by rw [mul_comm]; exact h2)⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · omega
    · exact hk
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_Icc] at hk ⊢
    refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
    · exact Nat.mul_pos (by omega) (by omega)
    · calc d * k ≤ d * (N / d) := Nat.mul_le_mul_left _ hk.2
        _ ≤ N := Nat.mul_div_le N d
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro k hk
    exact Nat.mul_div_cancel_left _ (by omega)
  · intro n hn
    simp only [Finset.mem_filter] at hn
    obtain ⟨k, rfl⟩ := hn.2
    rw [Nat.mul_div_cancel_left _ (by omega)]
    push_cast
    congr 1
    field_simp

end GppTotientVolterra
