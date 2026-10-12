import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The two-copy theta operator: exact finite algebra behind its Weyl law

Source: Codex, GPP-bridge PR #11 comment 6121782754 (2026-10-12), "theta-derived positive bulk
operator … exact two-term Riemann–von Mangoldt Weyl match". Codex's setup:
* the theta density is `Φ(x) = Σ_{n≥1} (4π²n⁴e^{9x/2} − 6πn²e^{5x/2}) e^{−πn²e^{2x}}`;
* `Ψ_α = Φ^α`, and `H_α = −d²/dx² + Ψ_α''/Ψ_α`;
* the eigenvalue count is `N_α(T) = T/(2π)[log(T/(πα)) − 1] + O(√T log T)`;
* only `α = 2` matches Riemann–von Mangoldt.

This file proves the exact algebraic and calculus steps:
* `summand_pos`: each summand of `Φ` is positive for `x ≥ 0` (because `2π > 3`).
* `hasDerivAt_Psi`, `hasDerivAt_Psi1`: for the leading-order model `log Ψ = α(−πe^{2x} + 9x/2 + K)`,
  `Ψ''/Ψ = 4α²π²e^{4x} − (18α² + 4α)πe^{2x} + 81α²/4`. At `α = 2` this is `−80π`
  (`Vmodel_two`). Codex's `O(1)` term for the true `Φ` includes the extra constant `−12α²` from the
  `e^{−2x}` correction; that analytic tail is not formalized.
* `wkb_integral`: the WKB phase integral in closed form, by the fundamental theorem of calculus:
  `∫₀^X √(T² − c²e^{4x}) dx = ½(T·log((T + √(T²−c²))/c) − √(T²−c²))`, `c e^{2X} = T`, `0 < c < T`.
* `weyl_constant_iff`: the constant `log(2T/c) − 1`, `c = 2πα`, equals Riemann–von Mangoldt's
  `log(T/2π) − 1` for all `T` iff `α = 2`. One parameter fits one constant. The `T log T/(2π)`
  coefficient comes from the `e^{4x}` growth.

**Not formalized, so ARGUED:** the Dirichlet gap, the compact resolvent, the bracketing remainder
`O(√T log T)`, and the UV trace asymptotics. They need unbounded Sturm–Liouville theory that Mathlib
lacks. Two-term Weyl agreement does not see `S(T)`, so this is a reference operator, not a zero
operator. **No RH claim.**
-/

namespace GppThetaTwoCopyWeyl

open Real

/-- Each summand of the theta density is positive for `x ≥ 0`. -/
theorem summand_pos {x n : ℝ} (hx : 0 ≤ x) (hn : 1 ≤ n) :
    0 < 4 * π ^ 2 * n ^ 4 * exp (9 * x / 2) - 6 * π * n ^ 2 * exp (5 * x / 2) := by
  have he : 1 ≤ exp (2 * x) := one_le_exp (by linarith)
  have hsplit : exp (9 * x / 2) = exp (5 * x / 2) * exp (2 * x) := by
    rw [← exp_add]; ring_nf
  have h2 : 6 < 2 * π * n ^ 2 * exp (2 * x) := by
    have hn2 : (1 : ℝ) ≤ n ^ 2 := one_le_pow₀ hn
    have hpi := pi_gt_three
    have hm : 1 * 1 ≤ n ^ 2 * exp (2 * x) := mul_le_mul hn2 he zero_le_one (by positivity)
    nlinarith
  have hfac : 4 * π ^ 2 * n ^ 4 * exp (9 * x / 2) - 6 * π * n ^ 2 * exp (5 * x / 2) =
      π * n ^ 2 * exp (5 * x / 2) * (2 * (2 * π * n ^ 2 * exp (2 * x)) - 6) := by
    rw [hsplit]; ring
  rw [hfac]
  have : 0 < n := by linarith
  have := pi_pos
  have : 0 < 2 * (2 * π * n ^ 2 * exp (2 * x)) - 6 := by linarith
  positivity

/-- Leading-order model of `Ψ_α = Φ^α`. -/
noncomputable def Psi (α K x : ℝ) : ℝ := exp (α * (-π * exp (2 * x) + 9 / 2 * x + K))

/-- `Ψ'`. -/
noncomputable def Psi1 (α K x : ℝ) : ℝ := Psi α K x * (α * (-2 * π * exp (2 * x) + 9 / 2))

/-- The model potential `Ψ''/Ψ`. -/
noncomputable def Vmodel (α x : ℝ) : ℝ :=
  4 * α ^ 2 * π ^ 2 * exp (4 * x) - (18 * α ^ 2 + 4 * α) * π * exp (2 * x) + 81 * α ^ 2 / 4

lemma hasDerivAt_exp2 (x : ℝ) : HasDerivAt (fun x => exp (2 * x)) (2 * exp (2 * x)) x := by
  have := HasDerivAt.exp (HasDerivAt.const_mul 2 (hasDerivAt_id' x))
  exact this.congr_deriv (by ring)

theorem hasDerivAt_Psi (α K x : ℝ) : HasDerivAt (Psi α K) (Psi1 α K x) x := by
  have hin : HasDerivAt (fun x => α * (-π * exp (2 * x) + 9 / 2 * x + K))
      (α * (-2 * π * exp (2 * x) + 9 / 2)) x := by
    have := HasDerivAt.const_mul α (((HasDerivAt.const_mul (-π) (hasDerivAt_exp2 x)).add
      (HasDerivAt.const_mul (9 / 2) (hasDerivAt_id' x))).add_const K)
    exact this.congr_deriv (by ring)
  exact (HasDerivAt.exp hin).congr_deriv (by unfold Psi1 Psi; ring)

/-- **The model potential.** `Ψ'' = Vmodel · Ψ`. -/
theorem hasDerivAt_Psi1 (α K x : ℝ) : HasDerivAt (Psi1 α K) (Psi α K x * Vmodel α x) x := by
  have hin : HasDerivAt (fun x => α * (-2 * π * exp (2 * x) + 9 / 2))
      (α * (-2 * π * (2 * exp (2 * x)))) x := by
    have := HasDerivAt.const_mul α ((HasDerivAt.const_mul (-2 * π) (hasDerivAt_exp2 x)).add_const
      (9 / 2))
    exact this.congr_deriv (by ring)
  have := (hasDerivAt_Psi α K x).mul hin
  refine this.congr_deriv ?_
  have h4 : exp (4 * x) = exp (2 * x) ^ 2 := by rw [← exp_nat_mul]; ring_nf
  unfold Psi1 Vmodel
  rw [h4]
  ring

/-- At `α = 2`: `V = 16π²e^{4x} − 80πe^{2x} + 81`. -/
theorem Vmodel_two (x : ℝ) :
    Vmodel 2 x = 16 * π ^ 2 * exp (4 * x) - 80 * π * exp (2 * x) + 81 := by
  unfold Vmodel; ring

/-- The WKB antiderivative. -/
noncomputable def F (T c x : ℝ) : ℝ :=
  (1 / 2) * (sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2) -
    T * log ((T + sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2)) / (c * exp (2 * x))))

lemma F_deriv_alg {T y W : ℝ} (hy : 0 < y) (hW : 0 < W) (hTW : 0 < T + W)
    (hW2 : W ^ 2 = T ^ 2 - y ^ 2) :
    1 / 2 * (-(2 * y * (2 * y)) / (2 * W) -
      T * ((-(2 * y * (2 * y)) / (2 * W) * y - (T + W) * (2 * y)) / y ^ 2 / ((T + W) / y))) = W := by
  have key : 1 / 2 * (-(2 * y * (2 * y)) / (2 * W) -
      T * ((-(2 * y * (2 * y)) / (2 * W) * y - (T + W) * (2 * y)) / y ^ 2 / ((T + W) / y))) =
      (T ^ 2 + T * W - y ^ 2) / (T + W) := by
    field_simp
    ring
  rw [key, show T ^ 2 + T * W - y ^ 2 = W * (T + W) by linear_combination (-1 : ℝ) * hW2]
  field_simp

lemma hasDerivAt_F {T c x : ℝ} (hc : 0 < c) (hT : 0 < T) (hx : c * exp (2 * x) < T) :
    HasDerivAt (F T c) (sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2)) x := by
  set y := c * exp (2 * x) with hydef
  have hy0 : 0 < y := by positivity
  have hq : 0 < T ^ 2 - y ^ 2 := by nlinarith
  set W := sqrt (T ^ 2 - y ^ 2) with hWdef
  have hW : 0 < W := sqrt_pos.mpr hq
  have hW2 : W ^ 2 = T ^ 2 - y ^ 2 := sq_sqrt hq.le
  have hy : HasDerivAt (fun x => c * exp (2 * x)) (2 * y) x :=
    (HasDerivAt.const_mul c (hasDerivAt_exp2 x)).congr_deriv (by ring)
  have hQ : HasDerivAt (fun x => T ^ 2 - (c * exp (2 * x)) ^ 2) (-(2 * y * (2 * y))) x :=
    (HasDerivAt.const_sub (T ^ 2) (HasDerivAt.fun_pow hy 2)).congr_deriv (by simp [hydef])
  have hS : HasDerivAt (fun x => sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2))
      (-(2 * y * (2 * y)) / (2 * W)) x := HasDerivAt.sqrt hQ hq.ne'
  have hL : HasDerivAt (fun x => log ((T + sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2)) /
      (c * exp (2 * x))))
      (((-(2 * y * (2 * y)) / (2 * W) * y - (T + W) * (2 * y)) / y ^ 2) / ((T + W) / y)) x := by
    have hdiv := HasDerivAt.fun_div (HasDerivAt.const_add T hS) hy hy0.ne'
    exact HasDerivAt.log hdiv (by positivity)
  have := HasDerivAt.const_mul (1 / 2) (hS.sub (HasDerivAt.const_mul T hL))
  refine this.congr_deriv ?_
  exact F_deriv_alg hy0 hW (by positivity) hW2

/-- **The WKB phase integral in closed form.** If `0 < c < T` and `c e^{2X} = T`, then
`∫₀^X √(T² − (c e^{2x})²) dx = ½(T log((T + √(T²−c²))/c) − √(T²−c²))`. -/
theorem wkb_integral {T c X : ℝ} (hc : 0 < c) (hcT : c < T) (hX : c * exp (2 * X) = T) :
    ∫ x in (0 : ℝ)..X, sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2) =
      (1 / 2) * (T * log ((T + sqrt (T ^ 2 - c ^ 2)) / c) - sqrt (T ^ 2 - c ^ 2)) := by
  have hT : 0 < T := hc.trans hcT
  have hX0 : 0 ≤ X := by
    by_contra h
    have h := lt_of_not_ge h
    have : exp (2 * X) < exp 0 := exp_lt_exp.mpr (by linarith)
    rw [exp_zero] at this
    nlinarith
  have hmono : ∀ x, x < X → c * exp (2 * x) < T := by
    intro x hx
    rw [← hX]
    exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr (by linarith)) hc
  have hcont : ContinuousOn (F T c) (Set.Icc 0 X) := by
    intro x hx
    have hpos : 0 < c * exp (2 * x) := by positivity
    have hnum : 0 < T + sqrt (T ^ 2 - (c * exp (2 * x)) ^ 2) := by positivity
    unfold F
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul continuousAt_const
    apply ContinuousAt.sub (by fun_prop)
    apply ContinuousAt.mul continuousAt_const
    exact ContinuousAt.log (ContinuousAt.div (by fun_prop) (by fun_prop) hpos.ne')
      (div_pos hnum hpos).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hX0 hcont
    (fun x hx => hasDerivAt_F hc hT (hmono x hx.2)) (by
      apply Continuous.intervalIntegrable; fun_prop)]
  unfold F
  rw [hX, sub_self, sqrt_zero, add_zero, div_self hT.ne', log_one]
  simp
  ring

/-- **One parameter fits one constant.** -/
theorem weyl_constant_iff {α : ℝ} (hα : 0 < α) :
    (∀ T : ℝ, 0 < T → log (2 * T / (2 * π * α)) - 1 = log (T / (2 * π)) - 1) ↔ α = 2 := by
  constructor
  · intro h
    have h1 := h (2 * π) (by positivity)
    have hp := pi_pos
    rw [div_self (by positivity), log_one, sub_left_inj] at h1
    have h2 : 2 * (2 * π) / (2 * π * α) = 2 / α := by field_simp
    rw [h2] at h1
    rcases log_eq_zero.mp h1 with h3 | h3 | h3
    · exact absurd h3 (by positivity)
    · field_simp at h3; linarith
    · have : 0 < 2 / α := by positivity
      linarith
  · rintro rfl T _
    congr 2
    field_simp

end GppThetaTwoCopyWeyl
