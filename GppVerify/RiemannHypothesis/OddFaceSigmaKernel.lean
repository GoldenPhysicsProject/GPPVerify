import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# OddFace(0.5), σ-rig: the kernel inequality `h(u) ≥ 1/u`, on its correct domain

Heart's Round 9 (GPP-bridge PR #11, comment 6890312805; GPPDiscovery5 `01a3951`) splits the
band-limited weight as `σ_x = 2C₀ + 6Cin(t/2) + 6R(t) + B(t) + P(t)` with
`R(t) = ∫₀^{1/2} (h(u) − 1/u)(1 − cos ut) du` and `h(u) = 2e^{−u/2}/(1 − e^{−2u})`. It drops `R`
from the σ-rig lower bound using `R ≥ 0`, which it derived from "`h ≥ 1/u` on `(0, ∞)`: PROVED".

Turbo's audit (6890419581) found that claim false as stated: `h(5) < 1/5`. The audit repaired it
on the domain the σ-rig actually uses, `(0, 1/2]`. Both halves are proved here:

* **`one_div_le_h`**: `1/u ≤ h(u)` for `0 < u ≤ 1`. This covers `(0, 1/2]`, so `R ≥ 0` holds
  pointwise in its integrand. The core is `sinh u ≤ u e^{u/2}` (`sinh_le_mul_exp_half`), from
  `e^{−u/2} ≥ 1 − u/2` and `(x − 1)²(1 + 2x − x²) ≥ 0` at `x = e^{u/2} ∈ [1, 2)`.
* **`h_five_lt`**: `h(5) < 1/5`. The unrestricted claim is false, as the audit says.

**Scope.** This is the one pointwise kernel fact under the σ-rig.
 Those are interval-certified NUMERICAL, not Lean. (T1′) is closed at that label
(`λ_Z ≥ 5.24628`). OddFace(0.5) is NUMERICAL; H_ψ, WeilIsGram, ARP and RH are OPEN.
No `sorry`, no axioms.
-/

namespace GppOddFaceSigma

open Real

/-- Heart's kernel `h(u) = 2e^{−u/2}/(1 − e^{−2u})` (which equals `e^{u/2}/sinh u`). -/
noncomputable def h (u : ℝ) : ℝ := 2 * exp (-u / 2) / (1 - exp (-2 * u))

/-- `sinh u ≤ u e^{u/2}` for `0 ≤ u ≤ 1`. -/
theorem sinh_le_mul_exp_half {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : sinh u ≤ u * exp (u / 2) := by
  set x := exp (u / 2) with hx
  set y := exp (-u / 2) with hy
  have hxy : x * y = 1 := by rw [hx, hy, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hx1 : 1 ≤ x := Real.one_le_exp (by linarith)
  have hy0 : 0 < y := Real.exp_pos _
  have hyl : 1 - u / 2 ≤ y := by
    have := Real.add_one_le_exp (-u / 2); rw [hy]; linarith
  have hx2 : x ^ 2 < 4 := by
    have e1 : x ^ 2 = exp u := by rw [hx, ← Real.exp_nat_mul]; ring_nf
    have e2 : exp u ≤ exp 1 := Real.exp_le_exp.2 hu1
    have e3 := Real.exp_one_lt_d9
    rw [e1]; linarith
  have hs : sinh u = (x ^ 2 - y ^ 2) / 2 := by
    rw [Real.sinh_eq, hx, hy, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; ring_nf
  rw [hs]
  -- `u x ≥ 2x(1 − y) = 2(x − 1)`, and `2(x − 1) ≥ (x² − y²)/2` by `(x−1)²(1 + 2x − x²) ≥ 0`.
  have h1 : 2 * (x - 1) ≤ u * x := by nlinarith
  have hyx : y = 1 / x := by field_simp; linarith
  have hxpos : 0 < x := by linarith
  have h2 : (x ^ 2 - y ^ 2) / 2 ≤ 2 * (x - 1) := by
    rw [hyx]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    have key : 0 ≤ (x - 1) ^ 2 * (1 + 2 * x - x ^ 2) := by
      apply mul_nonneg (sq_nonneg _); nlinarith
    have : x ^ 2 - (1 / x) ^ 2 = (x ^ 4 - 1) / x ^ 2 := by field_simp
    rw [this, div_le_iff₀ (by positivity)]
    nlinarith [key]
  linarith

/-- **`1/u ≤ h(u)` for `0 < u ≤ 1`** — in particular on `(0, 1/2]`, the domain of `R`. -/
theorem one_div_le_h {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) : 1 / u ≤ h u := by
  have hs := sinh_le_mul_exp_half hu0.le hu1
  set y := exp (-u / 2) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy4 : exp (-2 * u) = y ^ 4 := by rw [hy, ← Real.exp_nat_mul]; ring_nf
  have hylt : y < 1 := by rw [hy]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - y ^ 4 := by
    have : y ^ 4 < 1 := pow_lt_one₀ hy0.le hylt (by norm_num)
    linarith
  unfold h
  rw [hy4, ← hy, div_le_div_iff₀ hu0 hd]
  -- `sinh u ≤ u e^{u/2}`, multiplied through by `2y²`, is `1 − y⁴ ≤ 2uy`.
  have hx : exp (u / 2) * y = 1 := by rw [hy, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hsh : sinh u = (exp (u / 2) ^ 2 - y ^ 2) / 2 := by
    rw [Real.sinh_eq, hy, ← Real.exp_nat_mul, ← Real.exp_nat_mul]; ring_nf
  rw [hsh] at hs
  have hm := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℝ) ≤ 2 * y ^ 2)
  have e1 : (exp (u / 2) ^ 2 - y ^ 2) / 2 * (2 * y ^ 2) = (exp (u / 2) * y) ^ 2 - y ^ 4 := by ring
  have e2 : u * exp (u / 2) * (2 * y ^ 2) = 2 * u * y * (exp (u / 2) * y) := by ring
  rw [e1, e2, hx] at hm
  nlinarith

/-- **The unrestricted claim is false: `h(5) < 1/5`** (Turbo's audit 6890419581). -/
theorem h_five_lt : h 5 < 1 / 5 := by
  set y := exp (-5 / 2) with hy
  have hy0 : 0 < y := Real.exp_pos _
  have hy2 : y ^ 2 * exp 5 = 1 := by
    rw [hy, ← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he5 : (144 : ℝ) < exp 5 := by
    have h1 := Real.exp_one_gt_d9
    have : exp 5 = exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    calc (144 : ℝ) < 2.7182818283 ^ 5 := by norm_num
      _ < exp 1 ^ 5 := by gcongr
  have hsq : y ^ 2 * 144 < 1 := by
    nlinarith [mul_lt_mul_of_pos_left he5 (pow_pos hy0 2)]
  have hyl : y < 1 / 12 := by nlinarith
  have hy4 : exp (-2 * 5) = y ^ 4 := by rw [hy, ← Real.exp_nat_mul]; norm_num
  have hd : 0 < 1 - y ^ 4 := by nlinarith
  unfold h
  rw [show (-(5 : ℝ)) / 2 = -5 / 2 by ring, ← hy, hy4, div_lt_div_iff₀ hd (by norm_num)]
  nlinarith

end GppOddFaceSigma

#print axioms GppOddFaceSigma.one_div_le_h
#print axioms GppOddFaceSigma.h_five_lt
