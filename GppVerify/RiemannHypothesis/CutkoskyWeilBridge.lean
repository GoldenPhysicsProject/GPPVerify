import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Local shadow kernels and the finite-prime Weil kernel: the exact identities

From a 2026-08-22 research-front update to "Local-field shadow kernels, celestial unitarity,
and the adelic principal series": the proposed route
`celestial Cutkosky positivity → local shadow kernels → finite-prime Weil kernel → Casimir
compression → global Weil positivity → RH`. The final logical step (finite Weil paired-form
positivity on all nontrivial zeros ⟺ RH) is **already** proved unconditionally in
`GppVerify/RiemannHypothesis/WeilPositivityCriterion.lean` (`rh_iff_weil_pairedForm_nonneg`)
— that criterion is an *abstract* pairing over finite subsets of the actual (unknown) zero
set, not the classical Weil explicit-formula prime-sum quadratic form built here. Connecting
the two is itself a substantial, separate undertaking (the classical explicit formula linking
zeta zeros to prime sums via an integral transform) and is **not attempted in this file**.

This file formalizes only the exact, unconditional local identities: the finite-place shadow
kernel `K_p`, its vacuum-subtracted form `W_p`, and the Casimir-weighted Archimedean kernel
`H`'s positivity. **No claim toward RH, no claim of global Weil positivity, no axiom.** The
research question of whether a positivity-preserving projection from `K_p` to `K_p - 1`
exists is investigated numerically in `discovery/cutkosky_weil/` (answer, at the single-prime
level: no — see that directory's notes for the precise, rigorously-computed finding).
-/

namespace GppCutkoskyWeil

open Real

/-- The finite-place shadow kernel `K_p(t) = (1-p⁻¹)/|1-p^{-1/2-it}|²`, in its real
    closed form `(1-p⁻¹)/(1 - 2p^{-1/2}\cos(t\log p) + p^{-1})` (the modulus-squared
    denominator of the complex form, since `p^{-1/2+it} = \overline{p^{-1/2-it}}` for real
    `p,t`). -/
noncomputable def Kp (p t : ℝ) : ℝ :=
  (1 - p⁻¹) / (1 - 2 * p ^ (-(1:ℝ) / 2) * Real.cos (t * Real.log p) + p⁻¹)

/-- The vacuum-subtracted, log-weighted finite-place kernel: the local prime-frequency
    kernel appearing in the normalized Weil explicit formula. -/
noncomputable def Wp (p t : ℝ) : ℝ := Real.log p * (Kp p t - 1)

/-- `K_p(t) > 0` for `p > 1`: it is a Poisson kernel value, manifestly positive. -/
theorem Kp_pos {p : ℝ} (hp : 1 < p) (t : ℝ) : 0 < Kp p t := by
  have hp0 : (0:ℝ) < p := lt_trans one_pos hp
  have hr : p ^ (-(1:ℝ)/2) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by norm_num)
  have hrpos : 0 < p ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hp0 _
  have hnum : 0 < 1 - p⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp
  have hden : 0 < 1 - 2 * p ^ (-(1:ℝ)/2) * Real.cos (t * Real.log p) + p⁻¹ := by
    have hcos : Real.cos (t * Real.log p) ≤ 1 := Real.cos_le_one _
    have hval_sq : p ^ (-(1:ℝ)/2) * p ^ (-(1:ℝ)/2) = p⁻¹ := by
      rw [← Real.rpow_add hp0, show (-(1:ℝ)/2 + -(1:ℝ)/2) = (-1:ℝ) by ring,
        Real.rpow_neg_one]
    have hstrict : 0 < (1 - p ^ (-(1:ℝ)/2)) * (1 - p ^ (-(1:ℝ)/2)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [hstrict, mul_nonneg hrpos.le (sub_nonneg.mpr hcos), hval_sq]
  unfold Kp
  exact div_pos hnum hden

/-! ## The Casimir-weighted Archimedean kernel -/

/-- The celestial cut kernel, already derived (`discovery/shadow_ope/`,
    `GppVerify/QuantumGravity/LocalShadowKernel.lean`): `C(t) = t/(4\sinh(2\pi t))`. -/
noncomputable def cutKernel (t : ℝ) : ℝ := t / (4 * Real.sinh (2 * π * t))

/-- The Casimir-weighted Archimedean kernel `H(t) = (t²+1/4)·C(t)`, the rank-one
    principal-series Casimir eigenvalue `t²+1/4` times the celestial cut. -/
noncomputable def H (t : ℝ) : ℝ := (t ^ 2 + 1 / 4) * cutKernel t

/-- **`H(t) ≥ 0` for every real `t`**: `t` and `\sinh(2\pi t)` always share the same sign
    (both positive for `t>0`, both negative for `t<0`), so their ratio is nonnegative; at
    `t=0` the formula gives the junk value `0/0=0` (not the continuous extension
    `1/(32\pi)`, verified only numerically — see `discovery/cutkosky_weil/`), which is
    still `≥ 0`. -/
theorem H_nonneg (t : ℝ) : 0 ≤ H t := by
  unfold H cutKernel
  have hcasimir : (0:ℝ) ≤ t ^ 2 + 1 / 4 := by positivity
  apply mul_nonneg hcasimir
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have hsinh : Real.sinh (2 * π * t) < 0 :=
      Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg (by positivity) ht)
    exact le_of_lt (div_pos_of_neg_of_neg ht (by linarith))
  · simp [ht]
  · have hsinh : 0 < Real.sinh (2 * π * t) := Real.sinh_pos_iff.mpr (by positivity)
    exact le_of_lt (div_pos ht (by linarith))

end GppCutkoskyWeil
