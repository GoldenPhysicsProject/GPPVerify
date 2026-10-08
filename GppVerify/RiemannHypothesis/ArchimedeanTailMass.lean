import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The archimedean tail mass of the completed odd collision form

Source: `work/2026-10-08_astra_completed_odd_collision_trace.md`. The archimedean weight is
`a(y) = e^{y/2}/(e^y − e^{−y})`, and the finite-support mass
`M_∞(L) = log(8π) + γ + π/2 + log((1 − e^{−L/2})/(1 + e^{−L/2})) − 2 arctan(e^{−L/2})`
is the limiting mass `log(8π) + γ + π/2` minus `2 ∫_L^∞ a(y) dy`. This file proves the exact calculus
statement behind that last step, with `r = e^{-y/2}`:

* `tailPrim`: `G(y) = ½ log((1+r)/(1−r)) + arctan r` (`r = e^{-y/2}`) satisfies `G'(y) = −a(y)` for `y > 0`;
* `tail_integral`: `∫_L^∞ a(y) dy = G(L)` for `L > 0`;
* `tail_mass`: `2 ∫_L^∞ a(y) dy = −log((1 − e^{−L/2})/(1 + e^{−L/2})) + 2 arctan(e^{−L/2})`,
  so `M_∞(L) = C − 2∫_L^∞ a` with `C = log(8π)+γ+π/2` is exactly the displayed formula.

## Scope

Pure one-variable calculus. The constant `C`, the explicit formula that uses `M_∞`, and the positivity
of the completed odd form are not addressed. No RH claim.
-/

open Real MeasureTheory Filter Topology

namespace GppArchimedeanTail

/-- The archimedean weight `a(y) = e^{y/2}/(e^y − e^{−y})`. -/
noncomputable def a (y : ℝ) : ℝ := Real.exp (y / 2) / (Real.exp y - Real.exp (-y))

/-- `G(y) = ½ (log(1+r) − log(1−r)) + arctan r` with `r = e^{−y/2}` (i.e. `artanh r + arctan r`). -/
noncomputable def tailPrim (y : ℝ) : ℝ :=
  (1 / 2) * (Real.log (1 + Real.exp (-y / 2)) - Real.log (1 - Real.exp (-y / 2))) +
    Real.arctan (Real.exp (-y / 2))

/-- `a(y) = r/(1−r⁴)` with `r = e^{−y/2}`. -/
theorem a_eq (y : ℝ) (hr : Real.exp (-y / 2) ≠ 1) (hr0 : 0 < Real.exp (-y / 2)) :
    a y = Real.exp (-y / 2) / (1 - Real.exp (-y / 2) ^ 4) := by
  set r := Real.exp (-y / 2) with hrdef
  have e1 : Real.exp (y / 2) = r⁻¹ := by
    rw [hrdef, ← Real.exp_neg]; congr 1; ring
  have e2 : Real.exp y = (r⁻¹) ^ 2 := by
    rw [← e1, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (-y) = r ^ 2 := by
    rw [hrdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  unfold a
  rw [e1, e2, e3]
  have h4 : 1 - r ^ 4 ≠ 0 := by
    intro h
    have : r ^ 4 = 1 := by linarith
    have : r = 1 := by
      rcases (pow_eq_one_iff_of_nonneg hr0.le (by norm_num : (4 : ℕ) ≠ 0)).mp this with h; exact h
    exact hr this
  have hden : (r⁻¹) ^ 2 - r ^ 2 ≠ 0 := by
    intro h
    apply h4
    have : (r⁻¹) ^ 2 - r ^ 2 = (1 - r ^ 4) / r ^ 2 := by field_simp
    rw [this] at h
    field_simp at h
    linarith
  field_simp

theorem hasDerivAt_tailPrim {y : ℝ} (hy : 0 < y) : HasDerivAt tailPrim (-a y) y := by
  have hr : Real.exp (-y / 2) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show -y / 2 < 0 by linarith)
  have hr0 : 0 < Real.exp (-y / 2) := Real.exp_pos _
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (-y / 2)) (Real.exp (-y / 2) * (-1 / 2)) y := by
    have := ((hasDerivAt_id y).neg.div_const 2).exp
    simpa using this
  have hp : 1 + Real.exp (-y / 2) ≠ 0 := by linarith
  have hm : 1 - Real.exp (-y / 2) ≠ 0 := by linarith
  have h2 := (h1.const_add 1).log hp
  have h3 := (h1.const_sub 1).log hm
  have h4 := h1.arctan
  have h5 := ((h2.sub h3).const_mul (1 / 2 : ℝ)).add h4
  refine HasDerivAt.congr_deriv (f := tailPrim) h5 ?_
  rw [a_eq y hr.ne hr0]
  set r := Real.exp (-y / 2)
  have h4' : 1 - r ^ 4 ≠ 0 := by nlinarith [pow_pos hr0 4, pow_lt_one₀ hr0.le hr (by norm_num : (4:ℕ) ≠ 0)]
  have h2' : 1 + r ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem a_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ a y := by
  unfold a
  apply div_nonneg (Real.exp_pos _).le
  have : Real.exp (-y) < Real.exp y := Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem tendsto_tailPrim : Tendsto tailPrim atTop (𝓝 0) := by
  have hr : Tendsto (fun y : ℝ => Real.exp (-y / 2)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0:ℝ) < 2))
    refine this.congr fun y => ?_
    simp [neg_div]
  have h1 : Tendsto (fun y : ℝ => Real.log (1 + Real.exp (-y / 2))) atTop (𝓝 (Real.log (1 + 0))) :=
    ((tendsto_const_nhds.add hr).log (by norm_num))
  have h2 : Tendsto (fun y : ℝ => Real.log (1 - Real.exp (-y / 2))) atTop (𝓝 (Real.log (1 - 0))) :=
    ((tendsto_const_nhds.sub hr).log (by norm_num))
  have h3 : Tendsto (fun y : ℝ => Real.arctan (Real.exp (-y / 2))) atTop (𝓝 (Real.arctan 0)) :=
    (Real.continuous_arctan.tendsto 0).comp hr
  have := ((h1.sub h2).const_mul (1 / 2 : ℝ)).add h3
  have e : (0 : ℝ) = 1 / 2 * (Real.log (1 + 0) - Real.log (1 - 0)) + Real.arctan 0 := by simp
  rw [e]; exact this

/-- **The archimedean tail:** `∫_L^∞ a(y) dy = ½ log((1+r)/(1−r)) + arctan r`, `r = e^{−L/2}`. -/
theorem tail_integral {L : ℝ} (hL : 0 < L) : ∫ y in Set.Ioi L, a y = tailPrim L := by
  have hd : ∀ y ∈ Set.Ioi L, HasDerivAt (fun y => -tailPrim y) (a y) y := by
    intro y hy
    exact ((hasDerivAt_tailPrim (lt_trans hL hy)).neg).congr_deriv (neg_neg _)
  have hcont : ContinuousWithinAt (fun y => -tailPrim y) (Set.Ici L) L :=
    (hasDerivAt_tailPrim hL).neg.continuousAt.continuousWithinAt
  have hlim : Tendsto (fun y => -tailPrim y) atTop (𝓝 0) := by simpa using tendsto_tailPrim.neg
  have hint : IntegrableOn a (Set.Ioi L) :=
    integrableOn_Ioi_deriv_of_nonneg hcont hd (fun y hy => a_nonneg (lt_trans hL hy)) hlim
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hd hint hlim]
  ring

/-- **`2∫_L^∞ a = −log((1 − e^{−L/2})/(1 + e^{−L/2})) + 2 arctan(e^{−L/2})`**, the form in which
the tail enters `M_∞(L)`. -/
theorem tail_mass {L : ℝ} (hL : 0 < L) :
    2 * ∫ y in Set.Ioi L, a y =
      -Real.log ((1 - Real.exp (-L / 2)) / (1 + Real.exp (-L / 2))) +
        2 * Real.arctan (Real.exp (-L / 2)) := by
  have hr : Real.exp (-L / 2) < 1 := by
    simpa using Real.exp_lt_exp.mpr (show -L / 2 < 0 by linarith)
  have hr0 : 0 < Real.exp (-L / 2) := Real.exp_pos _
  rw [tail_integral hL, Real.log_div (by linarith) (by linarith)]
  unfold tailPrim
  ring

end GppArchimedeanTail
