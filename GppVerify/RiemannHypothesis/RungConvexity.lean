import GppVerify.RiemannHypothesis.AllPrimeGraphSquare
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The convex rung: `H(t) = 4(e^{t/2} + e^{−t/2} − 2) − V t + c`

On the rung between consecutive prime-power thresholds the Suzuki-type function in GPP's all-prime graph
flow (Turbo relay `b64da14`, §4) has the explicit form

`H(t) = 4(e^{t/2} + e^{−t/2} − 2) − V t + c`,  `H'(t) = D(t) = 2(e^{t/2} − e^{−t/2}) − V`,

with `V` the accumulated prime weight and `c` a rung constant. It is convex (`H'' = 2cosh(t/2) > 0`) with
minimiser `t* = 2 arsinh(V/4)`. This file proves, from the single inequality `e^x ≥ 1 + x` (tangent
lines of `exp`), the two-state convex-rung lemma used for the finite recurrence:

* `rungH_tangent`: `H(t) ≥ H(a) + D(a)(t − a)` for all `a, t`;
* `rungD_critical`: `D(t*) = 0` at `t* = 2 arsinh(V/4)`, and `rungH_min`: `H(t*) ≤ H(t)` for all `t`;
* `rung_clamped_min`: on any `[a, b]` the minimum of `H` is attained at the clamp of `t*` to `[a, b]`.

**Scope.** Calculus of one explicit convex function. It says nothing about the *values* of `V` and `c` along
the actual rung recurrence, and nothing about whether the rung minima stay nonnegative (a reserve invariant
that would be RH-equivalent; none is claimed).

No `sorry`, no axiom.
-/

open Real

noncomputable section

namespace GppRungConvexity

/-- `H(t) = 4(e^{t/2} + e^{−t/2} − 2) − V t + c`. -/
def rungH (V c t : ℝ) : ℝ := 4 * (Real.exp (t / 2) + Real.exp (-t / 2) - 2) - V * t + c

/-- `D(t) = 2(e^{t/2} − e^{−t/2}) − V`, the derivative of `H`. -/
def rungD (V t : ℝ) : ℝ := 2 * (Real.exp (t / 2) - Real.exp (-t / 2)) - V

/-- Tangent-line inequality for `exp`: `e^x ≥ e^a (1 + x − a)`. -/
theorem exp_tangent (a x : ℝ) : Real.exp a * (1 + (x - a)) ≤ Real.exp x := by
  have h := Real.add_one_le_exp (x - a)
  have e : Real.exp x = Real.exp a * Real.exp (x - a) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos a).le

/-- **Tangent inequality:** `H(t) ≥ H(a) + D(a) (t − a)`. -/
theorem rungH_tangent (V c a t : ℝ) : rungH V c a + rungD V a * (t - a) ≤ rungH V c t := by
  have h1 := exp_tangent (a / 2) (t / 2)
  have h2 := exp_tangent (-a / 2) (-t / 2)
  unfold rungH rungD
  have e1 : (1 + (t / 2 - a / 2)) = 1 + (t - a) / 2 := by ring
  have e2 : (1 + (-t / 2 - -a / 2)) = 1 - (t - a) / 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  nlinarith [h1, h2]

/-- `D` is nondecreasing. -/
theorem rungD_mono (V : ℝ) {s t : ℝ} (h : s ≤ t) : rungD V s ≤ rungD V t := by
  unfold rungD
  have h1 : Real.exp (s / 2) ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t / 2) ≤ Real.exp (-s / 2) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- **The critical point:** `D(2 arsinh(V/4)) = 0`. -/
theorem rungD_critical (V : ℝ) : rungD V (2 * Real.arsinh (V / 4)) = 0 := by
  unfold rungD
  have e1 : (2 * Real.arsinh (V / 4)) / 2 = Real.arsinh (V / 4) := by ring
  have e2 : -(2 * Real.arsinh (V / 4)) / 2 = -Real.arsinh (V / 4) := by ring
  rw [e1, e2]
  have h := Real.sinh_eq (Real.arsinh (V / 4))
  rw [Real.sinh_arsinh] at h
  linarith

/-- **Global minimum:** `H(t*) ≤ H(t)` for all `t`. -/
theorem rungH_min (V c t : ℝ) : rungH V c (2 * Real.arsinh (V / 4)) ≤ rungH V c t := by
  have h := rungH_tangent V c (2 * Real.arsinh (V / 4)) t
  rw [rungD_critical, zero_mul, add_zero] at h
  exact h

/-- The clamp of `t*` to `[a, b]`. -/
def clampPt (V a b : ℝ) : ℝ := max a (min b (2 * Real.arsinh (V / 4)))

/-- **Two-state convex-rung lemma:** on `[a, b]` the minimum of `H` is attained at the clamp of
`t* = 2 arsinh(V/4)` to `[a, b]`. -/
theorem rung_clamped_min (V c : ℝ) {a b : ℝ} (hab : a ≤ b) {t : ℝ} (ha : a ≤ t) (hb : t ≤ b) :
    rungH V c (clampPt V a b) ≤ rungH V c t := by
  set ts := 2 * Real.arsinh (V / 4) with hts
  unfold clampPt
  rw [← hts]
  by_cases h1 : ts < a
  · have hc : max a (min b ts) = a := by
      rw [min_eq_right (by linarith), max_eq_left h1.le]
    rw [hc]
    have hD : 0 ≤ rungD V a := by
      have := rungD_mono V h1.le
      rw [hts, rungD_critical] at this; exact this
    have := rungH_tangent V c a t
    nlinarith [mul_nonneg hD (sub_nonneg.mpr ha)]
  · by_cases h2 : b < ts
    · have hc : max a (min b ts) = b := by
        rw [min_eq_left h2.le, max_eq_right hab]
      rw [hc]
      have hD : rungD V b ≤ 0 := by
        have := rungD_mono V h2.le
        rw [hts, rungD_critical] at this; exact this
      have := rungH_tangent V c b t
      nlinarith [mul_nonneg (neg_nonneg.mpr hD) (sub_nonneg.mpr hb)]
    · rw [not_lt] at h1 h2
      have hc : max a (min b ts) = ts := by
        rw [min_eq_right h2, max_eq_right h1]
      rw [hc]
      exact rungH_min V c t

end GppRungConvexity

#print axioms GppRungConvexity.rung_clamped_min
#print axioms GppRungConvexity.rungH_tangent
