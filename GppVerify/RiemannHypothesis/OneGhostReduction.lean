import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# One-ghost reduction of the completed logarithmic derivative

Source: Codex, GPPDiscovery2 `research/2026-09-27_one_ghost_reduction_completed_log_derivative.md`.

The four-channel Krein square of `Δ_q(ξ'/ξ)` collapses to a positive Gamma tower plus one signed
prime-vs-continuum channel:
* `density_split`: `e^{−qx}/(1 − e^{−2x}) − e^{−qx} = e^{−(q+2)x}/(1 − e^{−2x})`. The `s = 0` pole square
  cancels the Gamma ground mode exactly.
* `density_sinh`: `e^{−(q+2)x}/(1 − e^{−2x}) = e^{−(q+1)x}/(2 sinh x)`. This is the `k = ½` SU(1,1) heat
  character `Tr e^{−2xK₀}`.
* `feature_identity`: the Gamma and `0`-pole feature products differ by exactly
  `w_{q+2}(x)(1 − e^{−ax})(1 − e^{−bx})`. This is the integrand form of the boxed identity.
* `gram_pointwise`: that integrand is a pointwise square in any finite combination, so the remainder
  `𝔇_{q+2}` is a Gram (positive) kernel whenever it is integrable.
* `baseline_closed_form`: the single surviving negative channel is
  `∫₀^∞ e^{−(q−1)x}(1 − e^{−ax})(1 − e^{−bx}) dx = 1/(q−1) − 1/(q−1+a) − 1/(q−1+b) + 1/(q−1+a+b)`.
* `baseline_eq_neg_pole_difference`: that value is `−Δ_q[1/(s − 1)](a, b)`, i.e. exactly the `s = 1` pole
  (PNT continuum) channel.

The Stieltjes form `∫ y^{−q}(…) d(ψ − y)` and the resolvent-trace form of `𝔇` are not formalized.
Fixed-`q` positivity still fails, as the note says. **No RH claim.**
-/

namespace GppOneGhost

open Real MeasureTheory Set

theorem density_split {q x : ℝ} (hx : 0 < x) :
    exp (-q * x) / (1 - exp (-2 * x)) - exp (-q * x)
      = exp (-(q + 2) * x) / (1 - exp (-2 * x)) := by
  have hd : 1 - exp (-2 * x) ≠ 0 := by
    have : exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have he : exp (-(q + 2) * x) = exp (-q * x) * exp (-2 * x) := by rw [← exp_add]; ring_nf
  rw [he, eq_div_iff hd, sub_mul, div_mul_cancel₀ _ hd]; ring

theorem density_sinh {q x : ℝ} (hx : 0 < x) :
    exp (-(q + 2) * x) / (1 - exp (-2 * x)) = exp (-(q + 1) * x) / (2 * sinh x) := by
  have hs : 0 < exp x - exp (-x) := by
    have := Real.exp_lt_exp.mpr (show -x < x by linarith); linarith
  have hd : 1 - exp (-2 * x) ≠ 0 := by
    have : exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [sinh_eq, div_eq_div_iff hd (by positivity)]
  have h1 : exp (-(q + 2) * x) = exp (-(q + 1) * x) * exp (-x) := by rw [← exp_add]; ring_nf
  have h2 : exp (-2 * x) = exp (-x) * exp (-x) := by rw [← exp_add]; ring_nf
  have h3 : exp x * exp (-x) = 1 := by rw [← exp_add]; simp
  rw [h1, h2]
  linear_combination exp (-(q + 1) * x) * h3

/-- The Gamma and `0`-pole features differ by the excited tower density. -/
theorem feature_identity {q a b x : ℝ} (hx : 0 < x) :
    (exp (-q * x / 2) / √(1 - exp (-2 * x)) * (1 - exp (-a * x))) *
        (exp (-q * x / 2) / √(1 - exp (-2 * x)) * (1 - exp (-b * x)))
      - (exp (-q * x / 2) * (1 - exp (-a * x))) * (exp (-q * x / 2) * (1 - exp (-b * x)))
      = exp (-(q + 2) * x) / (1 - exp (-2 * x)) * (1 - exp (-a * x)) * (1 - exp (-b * x)) := by
  have hpos : 0 < 1 - exp (-2 * x) := by
    have : exp (-2 * x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hsq : √(1 - exp (-2 * x)) * √(1 - exp (-2 * x)) = 1 - exp (-2 * x) :=
    mul_self_sqrt hpos.le
  have hhalf : exp (-q * x / 2) * exp (-q * x / 2) = exp (-q * x) := by rw [← exp_add]; ring_nf
  have hs : √(1 - exp (-2 * x)) ≠ 0 := (sqrt_pos.mpr hpos).ne'
  calc (exp (-q * x / 2) / √(1 - exp (-2 * x)) * (1 - exp (-a * x))) *
          (exp (-q * x / 2) / √(1 - exp (-2 * x)) * (1 - exp (-b * x)))
        - (exp (-q * x / 2) * (1 - exp (-a * x))) * (exp (-q * x / 2) * (1 - exp (-b * x)))
      = (exp (-q * x / 2) * exp (-q * x / 2)) / (√(1 - exp (-2 * x)) * √(1 - exp (-2 * x)))
          * (1 - exp (-a * x)) * (1 - exp (-b * x))
        - (exp (-q * x / 2) * exp (-q * x / 2)) * (1 - exp (-a * x)) * (1 - exp (-b * x)) := by
          ring
    _ = (exp (-q * x) / (1 - exp (-2 * x)) - exp (-q * x)) * (1 - exp (-a * x))
          * (1 - exp (-b * x)) := by rw [hsq, hhalf]; ring
    _ = _ := by rw [density_split hx]

/-- **Pointwise Gram form**: for weights `w ≥ 0`, every finite combination is a square. -/
theorem gram_pointwise {n : ℕ} (w x : ℝ) (hw : 0 ≤ w) (a c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (w * (1 - exp (-a i * x)) * (1 - exp (-a j * x))) := by
  have : ∑ i, ∑ j, c i * c j * (w * (1 - exp (-a i * x)) * (1 - exp (-a j * x)))
      = w * (∑ i, c i * (1 - exp (-a i * x))) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [this]; positivity

theorem integral_exp_neg {c : ℝ} (hc : 0 < c) : ∫ x in Ioi (0 : ℝ), exp (-c * x) = 1 / c := by
  have := integral_exp_mul_Ioi (a := -c) (by linarith) 0
  rw [this]; simp

theorem integrable_exp_neg {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => exp (-c * x)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith) 0

/-- **The surviving negative channel in closed form.** -/
theorem baseline_closed_form {q a b : ℝ} (hq : 1 < q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ x in Ioi (0 : ℝ), exp (-(q - 1) * x) * (1 - exp (-a * x)) * (1 - exp (-b * x))
      = 1 / (q - 1) - 1 / (q - 1 + a) - 1 / (q - 1 + b) + 1 / (q - 1 + a + b) := by
  have hpt : ∀ x : ℝ, exp (-(q - 1) * x) * (1 - exp (-a * x)) * (1 - exp (-b * x))
      = exp (-(q - 1) * x) - exp (-(q - 1 + a) * x) - exp (-(q - 1 + b) * x)
        + exp (-(q - 1 + a + b) * x) := by
    intro x
    have e1 : exp (-(q - 1 + a) * x) = exp (-(q - 1) * x) * exp (-a * x) := by
      rw [← exp_add]; ring_nf
    have e2 : exp (-(q - 1 + b) * x) = exp (-(q - 1) * x) * exp (-b * x) := by
      rw [← exp_add]; ring_nf
    have e3 : exp (-(q - 1 + a + b) * x) = exp (-(q - 1) * x) * exp (-a * x) * exp (-b * x) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [e1, e2, e3]; ring
  simp_rw [hpt]
  have i0 := integrable_exp_neg (c := q - 1) (by linarith)
  have i1 := integrable_exp_neg (c := q - 1 + a) (by linarith)
  have i2 := integrable_exp_neg (c := q - 1 + b) (by linarith)
  have i3 := integrable_exp_neg (c := q - 1 + a + b) (by linarith)
  rw [integral_add (f := fun x => exp (-(q - 1) * x) - exp (-(q - 1 + a) * x)
      - exp (-(q - 1 + b) * x)) (g := fun x => exp (-(q - 1 + a + b) * x)) ((i0.sub i1).sub i2) i3,
    integral_sub (f := fun x => exp (-(q - 1) * x) - exp (-(q - 1 + a) * x))
      (g := fun x => exp (-(q - 1 + b) * x)) (i0.sub i1) i2,
    integral_sub (f := fun x => exp (-(q - 1) * x)) (g := fun x => exp (-(q - 1 + a) * x)) i0 i1,
    integral_exp_neg (by linarith), integral_exp_neg (by linarith), integral_exp_neg (by linarith),
    integral_exp_neg (by linarith)]

/-- It is minus the four-point difference of the `s = 1` pole `1/(s − 1)`. -/
theorem baseline_eq_neg_pole_difference (q a b : ℝ) :
    1 / (q - 1) - 1 / (q - 1 + a) - 1 / (q - 1 + b) + 1 / (q - 1 + a + b)
      = -(1 / (q + a - 1) + 1 / (q + b - 1) - 1 / (q - 1) - 1 / (q + a + b - 1)) := by
  rw [show q + a - 1 = q - 1 + a by ring, show q + b - 1 = q - 1 + b by ring,
    show q + a + b - 1 = q - 1 + a + b by ring]
  ring

end GppOneGhost
