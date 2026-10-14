import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# The mirror Gram window: reflected evaluation vectors match only on the critical line

Source: Codex, GPP-bridge `work/codex/2026-10-13_mirror_gram_window_lemma.md` (PR #11 comment 6159282705).

For `z = δ + iγ` and its Hermitian mirror `Dz = −z̄`, the evaluation vectors
`v_z(x) = e^{z̄ x}` on `L²[−h, h]` have
`‖v_z‖² = ‖v_{Dz}‖² = ∫_{−h}^{h} e^{2δx} dx = sinh(2hδ)/δ` (and `2h` at `δ = 0`), while
`⟨v_z, v_{Dz}⟩ = ∫_{−h}^{h} 1 dx = 2h` because the phases cancel. This file proves the real
content:
* `norm_sq_eq`: `∫_{−h}^{h} e^{2δx} dx = sinh(2hδ)/δ` for `δ ≠ 0`.
* `gram_psd`: `2h ≤ sinh(2hδ)/δ`, so the reflected Gram `[[a, 2h],[2h, a]]` has eigenvalues
  `a ± 2h ≥ 0` for **every** `δ`. Positivity alone does not locate zeros.
* `overlap_lt_one`: the normalized overlap `2hδ / sinh(2hδ)` is `< 1` for `δ ≠ 0` (it is `1` only at
  `δ = 0`). The mirror pair coincides only on the critical line.
* `overlap_tendsto_zero`: for fixed `δ ≠ 0` the overlap tends to `0` as `h → ∞`.

Imposing rank-one mirror matching at the zeros of `ξ` is equivalent to RH. It is **not** derived
here; the shifted `F_θ` and Davenport–Heilbronn controls reject any universal imposed rule.
**No RH claim.**
-/

namespace GppMirrorGramWindow

open Real Filter Topology intervalIntegral

/-- `‖v_z‖² = ∫_{−h}^{h} e^{2δx} dx = sinh(2hδ)/δ`. -/
theorem norm_sq_eq {δ : ℝ} (hδ : δ ≠ 0) (h : ℝ) :
    ∫ x in (-h)..h, Real.exp (2 * δ * x) = Real.sinh (2 * h * δ) / δ := by
  have h2 : (2 * δ) ≠ 0 := by positivity
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) h2, integral_exp,
    Real.sinh_eq]
  field_simp
  ring_nf
  field_simp

/-- `y < sinh y` for `y > 0`. -/
theorem lt_sinh {y : ℝ} (hy : 0 < y) : y < Real.sinh y := Real.self_lt_sinh_iff.mpr hy

/-- **Positive semidefinite for every `δ`**: `2h ≤ sinh(2hδ)/δ`. -/
theorem gram_psd {δ h : ℝ} (hδ : δ ≠ 0) (hh : 0 ≤ h) : 2 * h ≤ Real.sinh (2 * h * δ) / δ := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · rw [le_div_iff_of_neg hneg]
    have : Real.sinh (2 * h * δ) ≤ 2 * h * δ := by
      rcases hh.lt_or_eq with hh' | hh'
      · have := lt_sinh (show 0 < 2 * h * -δ by nlinarith)
        rw [show 2 * h * -δ = -(2 * h * δ) by ring, Real.sinh_neg] at this
        linarith
      · subst hh'; simp
    linarith
  · rw [le_div_iff₀ hpos]
    rcases hh.lt_or_eq with hh' | hh'
    · exact (lt_sinh (by positivity)).le
    · subst hh'; simp

/-- **Mirror matching only on the line**: `2hδ / sinh(2hδ) < 1` for `h > 0`, `δ ≠ 0`. -/
theorem overlap_lt_one {δ h : ℝ} (hδ : δ ≠ 0) (hh : 0 < h) :
    2 * h * δ / Real.sinh (2 * h * δ) < 1 := by
  rcases lt_or_gt_of_ne hδ with hneg | hpos
  · have hy : 0 < 2 * h * -δ := by nlinarith
    have hs := lt_sinh hy
    rw [show 2 * h * -δ = -(2 * h * δ) by ring, Real.sinh_neg] at hs
    have hsn : Real.sinh (2 * h * δ) < 0 := by linarith
    rw [div_lt_one_of_neg hsn]; linarith
  · have hy : 0 < 2 * h * δ := by positivity
    rw [div_lt_one (by linarith [lt_sinh hy])]
    exact lt_sinh hy

/-- **The mirror pair decouples on large windows**: for fixed `δ ≠ 0`, `2hδ / sinh(2hδ) → 0`. -/
theorem overlap_tendsto_zero {δ : ℝ} (hδ : δ ≠ 0) :
    Tendsto (fun h : ℝ => 2 * h * δ / Real.sinh (2 * h * δ)) atTop (𝓝 0) := by
  -- y / sinh y → 0 as |y| → ∞; reduce to y = 2|δ| h → +∞ using evenness of y / sinh y
  have heven : ∀ y : ℝ, y / Real.sinh y = |y| / Real.sinh |y| := by
    intro y
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
    · rw [abs_of_neg hy, Real.sinh_neg, div_neg, neg_div, neg_neg]
  have hlin : Tendsto (fun h : ℝ => |2 * h * δ|) atTop atTop := by
    have : Tendsto (fun h : ℝ => (2 * |δ|) * h) atTop atTop :=
      tendsto_id.const_mul_atTop (by positivity)
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with h hh
    rw [abs_mul, abs_mul, abs_of_nonneg hh]; norm_num; ring
  have hkey : Tendsto (fun y : ℝ => y / Real.sinh y) atTop (𝓝 0) := by
    -- y / sinh y ≤ 2y e^{-y} / (1 - e^{-2y}) eventually; use y e^{-y} → 0
    have hsq : Tendsto (fun y : ℝ => y / Real.exp y) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1 |>.congr (fun y => by
        simp [Real.exp_neg, div_eq_mul_inv])
    have hb : ∀ y : ℝ, 1 ≤ y → 0 ≤ y / Real.sinh y ∧ y / Real.sinh y ≤ 4 * (y / Real.exp y) := by
      intro y hy
      have hs : 0 < Real.sinh y := Real.sinh_pos_iff.mpr (by linarith)
      refine ⟨by positivity, ?_⟩
      have he : Real.exp y ≤ 4 * Real.sinh y := by
        rw [Real.sinh_eq]
        have h1 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        have h2 : Real.exp (-1) < 1 / 2 := by
          have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num)
          rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; linarith
        have h3 : 1 ≤ Real.exp y := Real.one_le_exp (by linarith)
        nlinarith
      rw [div_le_iff₀ hs]
      calc y = 4 * (y / Real.exp y) * (Real.exp y / 4) := by field_simp
        _ ≤ 4 * (y / Real.exp y) * Real.sinh y := by
          gcongr
          · have : 0 ≤ y / Real.exp y := by positivity
            linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hsq.const_mul 4) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with y hy; exact (hb y hy).1
    · filter_upwards [eventually_ge_atTop 1] with y hy; exact (hb y hy).2
  exact (hkey.comp hlin).congr fun h => (heven _).symm

end GppMirrorGramWindow
