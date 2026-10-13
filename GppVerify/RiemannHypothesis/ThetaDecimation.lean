import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Theta decimation: the summands of the Riemann theta density rescale under primes

Source: Codex, GPP-bridge `research/codex/2026-09-30_theta_decimation_dyadic_boundary.md`.

With `φ_n(u) = (4π²n⁴e^{9u/2} − 6πn²e^{5u/2}) e^{−πn²e^{2u}}` (so `Φ = Σ_n φ_n`):
* `phi_scaling`: **`φ_n(u) = n^{−1/2} φ_1(u + log n)`** for `n > 0`.
* `phi_decimation`: with `a_p = ½ log p`, **`φ_{pm}(u − a_p) = p^{−1/2} φ_m(u + a_p)`**. This is the
  exact orthogonal realization of the local half-density factor `p^{−1/2}`.
* `threshold_iff`: the two tail exponents `−π(2e^{2t} − 1)e^{2u}` and `−π(2e^{−2t} − 1)e^{−2u}` are
  both decaying iff **`|t| < ½ log 2`**. That is the algebraic core of the note's dyadic threshold
  `g_t ∈ L²(μ) ⟺ |t| < ½ log 2`.

**Scope.** The `L²` membership itself rests on the tail asymptotics `Φ(u) = e^{O(u)}e^{−πe^{2u}}`.
Those, and the reflected left tail, are ARGUED and not formalized here. The orthogonal-projection
identity `‖Φ(u−a_p)‖² = p^{−1}‖Φ(u+a_p)‖² + ‖(I−P_p)Φ(u−a_p)‖²` follows from `phi_decimation`
plus Pythagoras in `ℓ²`, which is not formalized. **No RH claim.**
-/

namespace GppThetaDecimation

open Real

/-- The `n`-th summand of the theta density. -/
noncomputable def phi (n : ℝ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * n ^ 4 * exp (9 * u / 2) - 6 * π * n ^ 2 * exp (5 * u / 2)) *
    exp (-π * n ^ 2 * exp (2 * u))

lemma exp_add_log {n : ℝ} (hn : 0 < n) (c u : ℝ) :
    exp (c * (u + log n)) = n ^ c * exp (c * u) := by
  rw [mul_add, exp_add, mul_comm c (log n), ← rpow_def_of_pos hn, mul_comm]

/-- **Theta scaling.** -/
theorem phi_scaling {n : ℝ} (hn : 0 < n) (u : ℝ) :
    phi n u = n ^ (-(1 / 2 : ℝ)) * phi 1 (u + log n) := by
  unfold phi
  have h9 : exp (9 * (u + log n) / 2) = n ^ ((9 : ℝ) / 2) * exp (9 * u / 2) := by
    rw [show 9 * (u + log n) / 2 = (9 / 2) * (u + log n) by ring, exp_add_log hn,
      show (9 / 2 : ℝ) * u = 9 * u / 2 by ring]
  have h5 : exp (5 * (u + log n) / 2) = n ^ ((5 : ℝ) / 2) * exp (5 * u / 2) := by
    rw [show 5 * (u + log n) / 2 = (5 / 2) * (u + log n) by ring, exp_add_log hn,
      show (5 / 2 : ℝ) * u = 5 * u / 2 by ring]
  have h2 : exp (2 * (u + log n)) = n ^ 2 * exp (2 * u) := by
    rw [exp_add_log hn, show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  rw [h9, h5, h2]
  have e1 : n ^ (-(1 / 2 : ℝ)) * n ^ ((9 : ℝ) / 2) = n ^ 4 := by
    rw [← rpow_add hn, show -(1 / 2 : ℝ) + 9 / 2 = ((4 : ℕ) : ℝ) by norm_num, rpow_natCast]
  have e2 : n ^ (-(1 / 2 : ℝ)) * n ^ ((5 : ℝ) / 2) = n ^ 2 := by
    rw [← rpow_add hn, show -(1 / 2 : ℝ) + 5 / 2 = ((2 : ℕ) : ℝ) by norm_num, rpow_natCast]
  have hX : exp (-π * (1 : ℝ) ^ 2 * (n ^ 2 * exp (2 * u))) = exp (-π * n ^ 2 * exp (2 * u)) := by
    ring_nf
  rw [hX]
  linear_combination (-(4 * π ^ 2 * exp (9 * u / 2) * exp (-π * n ^ 2 * exp (2 * u)))) * e1 +
    (6 * π * exp (5 * u / 2) * exp (-π * n ^ 2 * exp (2 * u))) * e2

/-- **Prime decimation.** `φ_{pm}(u − a_p) = p^{−1/2} φ_m(u + a_p)` with `a_p = ½ log p`. -/
theorem phi_decimation {p m : ℝ} (hp : 0 < p) (hm : 0 < m) (u : ℝ) :
    phi (p * m) (u - log p / 2) = p ^ (-(1 / 2 : ℝ)) * phi m (u + log p / 2) := by
  rw [phi_scaling (mul_pos hp hm), phi_scaling hm, log_mul hp.ne' hm.ne',
    mul_rpow hp.le hm.le]
  rw [show u - log p / 2 + (log p + log m) = u + log p / 2 + log m by ring]
  ring

/-- **The dyadic threshold, algebraically.** -/
theorem threshold_iff (t : ℝ) :
    (1 < 2 * exp (2 * t) ∧ 1 < 2 * exp (-2 * t)) ↔ |t| < log 2 / 2 := by
  have hl2 : 0 < log 2 := log_pos one_lt_two
  have key : ∀ x : ℝ, 1 < 2 * exp x ↔ -log 2 < x := by
    intro x
    rw [show 2 * exp x = exp (x + log 2) by rw [exp_add, exp_log two_pos]; ring, ← exp_zero,
      exp_lt_exp]
    constructor <;> intro h <;> linarith
  rw [key, key, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

end GppThetaDecimation
