import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The logistic density, the `tanh(x/2)` substitution, and Möbius boosts

Source: Codex, GPPDiscovery2 `research/2026-10-02_logistic_compact_principal_series_bridge.md`,
§§2–4 (the exact calculus identities).

Let `p(x) = 1/(4 cosh²(x/2)) = eˣ/(1 + eˣ)²` be the logistic density and `r = tanh(x/2)`.

* `logistic_density_eq`: the two closed forms of `p` agree;
* `hasDerivAt_tanh_half`: `d/dx tanh(x/2) = 2 p(x)`, so `p(x) dx = ½ dr` — the substitution that sends
  the logistic line to the interval `(−1, 1)` with the flat measure;
* `tanh_half_sub`: the boost `x ↦ x − t` acts on `r` by the Möbius map
  `tanh((x − t)/2) = (r − a)/(1 − a r)`, `a = tanh(t/2)`;
* `hasDerivAt_mobius`: its derivative is `(1 − a²)/(1 − a r)²`.

## Checks and scope

All claims check. **Not formalized:** the Mellin/Laplace ratio representation, the compact
principal-series (circle) interpretation of the boost action, the Hilbert-space unitarity of the
boost on `L²(p dx)`, and everything in the note beyond §§2–4. This is calculus, not a statement
about `ζ`. No RH claim.
-/

open Real

namespace GppLogisticBoost

/-- The logistic density `p(x) = 1/(4 cosh²(x/2))`. -/
noncomputable def p (x : ℝ) : ℝ := 1 / (4 * Real.cosh (x / 2) ^ 2)

/-- **Two closed forms of the logistic density.** -/
theorem logistic_density_eq (x : ℝ) : p x = Real.exp x / (1 + Real.exp x) ^ 2 := by
  unfold p
  have h : Real.cosh (x / 2) = (Real.exp (x / 2) + Real.exp (-(x / 2))) / 2 := Real.cosh_eq _
  have e1 : Real.exp x = Real.exp (x / 2) ^ 2 := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-(x / 2)) = (Real.exp (x / 2))⁻¹ := Real.exp_neg _
  have hp : 0 < Real.exp (x / 2) := Real.exp_pos _
  rw [h, e2, e1]
  field_simp
  ring

theorem p_pos (x : ℝ) : 0 < p x := by
  unfold p; have := Real.cosh_pos (x / 2); positivity

/-- **The substitution `r = tanh(x/2)`**: `dr/dx = 2 p(x)`. -/
theorem hasDerivAt_tanh_half (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.tanh (x / 2)) (2 * p x) x := by
  have hc : Real.cosh (x / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hin : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := (hasDerivAt_id x).div_const 2
  have hs := (Real.hasDerivAt_sinh (x / 2)).comp x hin
  have hco := (Real.hasDerivAt_cosh (x / 2)).comp x hin
  have h := hs.div hco hc
  have e : (fun x : ℝ => Real.tanh (x / 2)) = (Real.sinh ∘ fun x : ℝ => x / 2) / (Real.cosh ∘ fun x : ℝ => x / 2) := by
    funext y; simp [Real.tanh_eq_sinh_div_cosh]
  rw [e]
  refine h.congr_deriv ?_
  unfold p
  have := Real.cosh_sq (x / 2)
  simp only [Function.comp]
  field_simp
  nlinarith [this]

/-- **Boosts act by Möbius maps**: `tanh((x − t)/2) = (r − a)/(1 − a r)`. -/
theorem tanh_half_sub (x t : ℝ) :
    Real.tanh ((x - t) / 2) =
      (Real.tanh (x / 2) - Real.tanh (t / 2)) / (1 - Real.tanh (t / 2) * Real.tanh (x / 2)) := by
  have hx := (Real.cosh_pos (x / 2)).ne'
  have ht := (Real.cosh_pos (t / 2)).ne'
  have hd : 0 < Real.cosh (x / 2) * Real.cosh (t / 2) - Real.sinh (x / 2) * Real.sinh (t / 2) := by
    rw [← Real.cosh_sub]; exact Real.cosh_pos _
  have e : (x - t) / 2 = x / 2 - t / 2 := by ring
  rw [e, Real.tanh_eq_sinh_div_cosh, Real.sinh_sub, Real.cosh_sub, Real.tanh_eq_sinh_div_cosh,
    Real.tanh_eq_sinh_div_cosh]
  have hd' : 1 - Real.sinh (t / 2) / Real.cosh (t / 2) * (Real.sinh (x / 2) / Real.cosh (x / 2)) ≠ 0 := by
    have : 1 - Real.sinh (t / 2) / Real.cosh (t / 2) * (Real.sinh (x / 2) / Real.cosh (x / 2)) =
        (Real.cosh (x / 2) * Real.cosh (t / 2) - Real.sinh (x / 2) * Real.sinh (t / 2)) /
          (Real.cosh (x / 2) * Real.cosh (t / 2)) := by field_simp
    rw [this]; positivity
  have hd2 := hd.ne'
  field_simp

/-- **Derivative of the Möbius boost** `r ↦ (r − a)/(1 − a r)`. -/
theorem hasDerivAt_mobius (a r : ℝ) (h : 1 - a * r ≠ 0) :
    HasDerivAt (fun r : ℝ => (r - a) / (1 - a * r)) ((1 - a ^ 2) / (1 - a * r) ^ 2) r := by
  have h1 : HasDerivAt (fun r : ℝ => r - a) 1 r := (hasDerivAt_id r).sub_const a
  have h2 : HasDerivAt (fun r : ℝ => 1 - a * r) (-a) r := by
    simpa using ((hasDerivAt_id r).const_mul a).const_sub 1
  refine (h1.div h2 h).congr_deriv ?_
  field_simp
  ring

end GppLogisticBoost
