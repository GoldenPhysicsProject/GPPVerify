import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Shadow boosts, positive-metric rigidity and prime shadow fidelity

Source: Codex, GPPDiscovery2 `research/2026-09-29_shadow_kms_boost_rigidity.md` §§1, 3–7.
§2 (the prime TFD block's eigenvalues `β/2`, `1/(2β)` and determinant `¼`) is already in
`PrimeSqrtHypercube`. The one-scale shadow-norm criterion is `ShadowKMSRigidity`.

* `mobius_add`: with `β(q) = (q − 1)/(q + 1)` for `q = √x > 0`, `β(qr) = (β q + β r)/(1 + β q β r)`.
  Multiplication becomes Einstein velocity addition (§1).
* `boost_split_unitary`: for any real `δ`, `diag(e^{−δt}, e^{δt})` preserves the split form
  `J = [[0,1],[1,0]]`. Off-line zero pairs are Krein-unitary boosts (§3).
* `rigidity`: if a metric with positive `(1,1)` entry `g` is invariant, i.e. `e^{−2δt} g = g` at
  one `t ≠ 0`, then `δ = 0` (§4). Conditional only: the missing bridge is that zeros induce such an
  invariant positive sector (§8).
* `fidelity_le_one`, `fidelity_eq_one_iff`: the prime shadow overlap
  `F_p(σ) = √((1−p^{−2σ})(1−p^{−2(1−σ)}))/(1−p^{−1}) ≤ 1`, with equality iff `σ = ½` (§5).
* `one_sub_fidelity_sq`: `(1−p^{−1})² − (1−p^{−2σ})(1−p^{−2(1−σ)}) = p^{−1}(p^{δ} − p^{−δ})²`
  with `δ = σ − ½` (§6). **Not formalized:** the product `∏_p F_p(σ) = 0` for `σ ≠ ½`, which
  combines this defect with `Σ 1/p = ∞`.
* `modular_spectrum_rigidity`: `1 − p^{−2σ} = 1 − p^{−2(1−σ)}` with `p > 1` forces `σ = ½` (§7).

**No RH claim.**
-/

namespace GppShadowBoostFidelity

open Real

/-- Square-root Cayley velocity `β(q) = (q − 1)/(q + 1)`. -/
noncomputable def beta (q : ℝ) : ℝ := (q - 1) / (q + 1)

/-- **Einstein addition**: prime multiplication is boost-rapidity addition. -/
theorem mobius_add {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    beta (q * r) = (beta q + beta r) / (1 + beta q * beta r) := by
  unfold beta
  have h1 : q + 1 ≠ 0 := by linarith
  have h2 : r + 1 ≠ 0 := by linarith
  have h3 : q * r + 1 ≠ 0 := by nlinarith
  have h4 : (q + 1) * (r + 1) + (q - 1) * (r - 1) ≠ 0 := by nlinarith
  field_simp
  ring

/-- **Split-unitary boost**: `diag(a, a⁻¹)` preserves `J = [[0,1],[1,0]]` (entrywise `Vᵀ J V = J`). -/
theorem boost_split_unitary (δ t : ℝ) :
    exp (-δ * t) * exp (δ * t) = 1 ∧ exp (δ * t) * exp (-δ * t) = 1 := by
  constructor <;> rw [← exp_add] <;> simp

/-- **Positive-metric rigidity**: an invariant positive `(1,1)` entry forces `δ = 0`. -/
theorem rigidity {δ t g : ℝ} (ht : t ≠ 0) (hg : 0 < g) (hinv : exp (-2 * δ * t) * g = g) :
    δ = 0 := by
  have h1 : exp (-2 * δ * t) = 1 := by
    have := congrArg (· / g) hinv
    simpa [hg.ne'] using this
  have h2 : -2 * δ * t = 0 := by simpa using h1
  have : δ * t = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_right ht

/-- Prime shadow overlap `F_p(σ)`. -/
noncomputable def fidelity (p σ : ℝ) : ℝ :=
  sqrt ((1 - p ^ (-2 * σ)) * (1 - p ^ (-2 * (1 - σ)))) / (1 - p⁻¹)

/-- **Orthogonality defect**: `(1−p⁻¹)² − (1−x)(1−y) = p⁻¹(p^δ − p^{−δ})²`. -/
theorem one_sub_fidelity_sq {p σ : ℝ} (hp : 0 < p) :
    (1 - p⁻¹) ^ 2 - (1 - p ^ (-2 * σ)) * (1 - p ^ (-2 * (1 - σ))) =
      p⁻¹ * (p ^ (σ - 1 / 2) - p ^ (-(σ - 1 / 2))) ^ 2 := by
  have e1 : p ^ (-2 * σ) * p ^ (-2 * (1 - σ)) = p⁻¹ ^ 2 := by
    rw [← rpow_add hp, show -2 * σ + -2 * (1 - σ) = (-1 : ℝ) * 2 by ring, rpow_mul hp.le,
      rpow_neg_one]; norm_cast
  have e2 : p⁻¹ * (p ^ (σ - 1 / 2)) ^ 2 = p ^ (-2 * (1 - σ)) := by
    rw [← rpow_natCast (p ^ (σ - 1 / 2)) 2, ← rpow_mul hp.le, ← rpow_neg_one, ← rpow_add hp]
    congr 1; push_cast; ring
  have e3 : p⁻¹ * (p ^ (-(σ - 1 / 2))) ^ 2 = p ^ (-2 * σ) := by
    rw [← rpow_natCast (p ^ (-(σ - 1 / 2))) 2, ← rpow_mul hp.le, ← rpow_neg_one, ← rpow_add hp]
    congr 1; push_cast; ring
  have e4 : p ^ (σ - 1 / 2) * p ^ (-(σ - 1 / 2)) = 1 := by
    rw [← rpow_add hp]; simp
  have : p⁻¹ * (p ^ (σ - 1 / 2) - p ^ (-(σ - 1 / 2))) ^ 2 =
      p⁻¹ * (p ^ (σ - 1 / 2)) ^ 2 + p⁻¹ * (p ^ (-(σ - 1 / 2))) ^ 2 -
        2 * p⁻¹ * (p ^ (σ - 1 / 2) * p ^ (-(σ - 1 / 2))) := by ring
  rw [this, e2, e3, e4]
  nlinarith [e1]

theorem fidelity_le_one {p σ : ℝ} (hp : 1 < p) : fidelity p σ ≤ 1 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < 1 - p⁻¹ := by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp
  unfold fidelity
  rw [div_le_one hd, sqrt_le_left hd.le]
  have := one_sub_fidelity_sq (σ := σ) hp0
  have : 0 ≤ p⁻¹ * (p ^ (σ - 1 / 2) - p ^ (-(σ - 1 / 2))) ^ 2 := by positivity
  linarith

theorem fidelity_eq_one_iff {p σ : ℝ} (hp : 1 < p) : fidelity p σ = 1 ↔ σ = 1 / 2 := by
  have hp0 : 0 < p := by linarith
  have hd : 0 < 1 - p⁻¹ := by rw [sub_pos]; exact inv_lt_one_of_one_lt₀ hp
  have key := one_sub_fidelity_sq (σ := σ) hp0
  constructor
  · intro h
    unfold fidelity at h
    rw [div_eq_one_iff_eq hd.ne'] at h
    have hx : 0 ≤ (1 - p ^ (-2 * σ)) * (1 - p ^ (-2 * (1 - σ))) := by
      by_contra hneg
      push Not at hneg
      rw [sqrt_eq_zero'.mpr hneg.le] at h
      exact hd.ne' h.symm
    have hsq := congrArg (· ^ 2) h
    simp only [sq_sqrt hx] at hsq
    have h0 : p⁻¹ * (p ^ (σ - 1 / 2) - p ^ (-(σ - 1 / 2))) ^ 2 = 0 := by rw [← key, hsq]; ring
    have hpinv : p⁻¹ ≠ 0 := inv_ne_zero hp0.ne'
    have h1 : p ^ (σ - 1 / 2) = p ^ (-(σ - 1 / 2)) := by
      have := (mul_eq_zero.mp h0).resolve_left hpinv
      exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
    have h2 : σ - 1 / 2 = -(σ - 1 / 2) := by
      have := congrArg (logb p) h1
      rwa [logb_rpow hp0 hp.ne', logb_rpow hp0 hp.ne'] at this
    linarith
  · intro h
    subst h
    unfold fidelity
    have : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [this, ← sq, sqrt_sq]
    · rw [div_eq_one_iff_eq hd.ne', show (-2 : ℝ) * (1 / 2) = -1 by norm_num, rpow_neg_one]
    · rw [show (-2 : ℝ) * (1 / 2) = -1 by norm_num, rpow_neg_one]; exact hd.le

/-- **Modular-spectrum rigidity** at one prime. -/
theorem modular_spectrum_rigidity {p σ : ℝ} (hp : 1 < p)
    (h : 1 - p ^ (-2 * σ) = 1 - p ^ (-2 * (1 - σ))) : σ = 1 / 2 := by
  have hp0 : 0 < p := by linarith
  have h1 : p ^ (-2 * σ) = p ^ (-2 * (1 - σ)) := by linarith
  have := congrArg (logb p) h1
  rw [logb_rpow hp0 hp.ne', logb_rpow hp0 hp.ne'] at this
  linarith

end GppShadowBoostFidelity
