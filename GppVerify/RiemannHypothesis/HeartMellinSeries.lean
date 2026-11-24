/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statements from Heart of the Cosmos / Grok)
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Mellin and series identities from GPPDiscovery5 Rounds 15–22 (batch 2)

Formalization of claims from Heart of the Cosmos's request (bridge `CONVERSATION-week-025`,
"Formalization requests from Heart (Rounds 15–22)"); claim numbers and `HR<round>_` names follow
that entry.

* #11 `HR18_truncated_primary_L2_iff`, `HR18_truncated_primary_norm_sq`: the truncated primary
  `e_ρ(x) = x^{ρ̄−1}·1_{(0,1)}(x)` lies in `L²` iff `Re ρ > 1/2`, and then `‖e_ρ‖² = 1/(2 Re ρ − 1)`.
* #13 `HR_theta_functional_equation`, `HR19_lattice_state_shadow_invariant`: the real-variable theta
  functional equation `1 + 2θ₊(1/y) = √y (1 + 2θ₊(y))` (from Mathlib's `jacobiTheta_S_smul`) and
  `x⁻¹ F_ζ(1/x) = F_ζ(x)` for `F_ζ(x) = θ₊(x²) − 1/(2x)`.
* #22 `HR21_mellin_convolution_diagonal`: the Mellin convolution acts diagonally on power functions,
  `∫ F(x/y) y^{−s} dy/y = x^{−s} M_F(s)`.
* #23 `HR21_riemann_split`, `HR21_riemann_split_critical`, `HR21_riemann_split_critical_zero_iff`: for
  `F` with `x⁻¹ F(x⁻¹) = F(x)`, `M_F(s) = A(s) + A(1 − s)`, `A(s) = ∫_1^∞ x^{s−1} F(x) dx`; for real `F`
  on the critical line `M_F(1/2 + it) = 2 Re A(1/2 + it)`, which vanishes iff `Re A` does.
* #24 `HR_thetaPlus_one_lt_half`, `HR_x_thetaPlus_le`, `HR21_lattice_state_negative_right`,
  `HR21_phi_negative`, `HR21_hankel_form_negative`: `F_ζ(x) < 0` for `x ≥ 1` (elementary: `x e^{−πn²x²} ≤
  e^{−πn²}` from `e^t ≥ 1 + t`, and `θ₊(1) < 1/2`), `φ(u) = e^{u/2} F_ζ(e^u) < 0` for `u ≥ 0`, and the
  cross-boundary Hankel form `∫∫ f(u) φ(u+v) f(v)` is strictly negative for measurable `f ≥ 0` positive on
  a set of positive measure (with the integrand integrable).

No zeta zero is an input; all statements are unconditional calculus. No `sorry`, no `axiom`.
-/

namespace GppHeartMellin

open MeasureTheory Set Complex
open scoped ComplexConjugate

/-! ## #11 The truncated primary is in `L²` iff `Re ρ > 1/2` -/

/-- `e_ρ(x) = x^{ρ̄ − 1}` on `(0, 1)`, and `0` elsewhere. -/
noncomputable def HR18_e (ρ : ℂ) : ℝ → ℂ :=
  Set.indicator (Set.Ioo (0 : ℝ) 1) (fun x : ℝ => (x : ℂ) ^ (conj ρ - 1))

private theorem HR18_norm_sq (ρ : ℂ) (x : ℝ) :
    ‖HR18_e ρ x‖ ^ 2
      = Set.indicator (Set.Ioo (0 : ℝ) 1) (fun x : ℝ => x ^ (2 * (ρ.re - 1))) x := by
  by_cases hx : x ∈ Set.Ioo (0 : ℝ) 1
  · rw [Set.indicator_of_mem hx, HR18_e, Set.indicator_of_mem hx,
      Complex.norm_cpow_eq_rpow_re_of_pos hx.1]
    have : (conj ρ - 1).re = ρ.re - 1 := by simp
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]
    congr 1
    push_cast
    ring
  · rw [Set.indicator_of_notMem hx, HR18_e, Set.indicator_of_notMem hx]
    simp

private theorem HR18_measurable (ρ : ℂ) : Measurable (HR18_e ρ) :=
  Measurable.indicator (by fun_prop) measurableSet_Ioo

/-- **#11.** `e_ρ ∈ L²(ℝ, dx)` iff `Re ρ > 1/2`. -/
theorem HR18_truncated_primary_L2_iff (ρ : ℂ) :
    MemLp (HR18_e ρ) 2 volume ↔ 1 / 2 < ρ.re := by
  rw [memLp_two_iff_integrable_sq_norm (HR18_measurable ρ).aestronglyMeasurable]
  simp_rw [HR18_norm_sq]
  rw [integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
    ← IntegrableOn, intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

/-- **#11 (value).** For `Re ρ > 1/2`, `‖e_ρ‖²_{L²} = 1/(2 Re ρ − 1)`. -/
theorem HR18_truncated_primary_norm_sq {ρ : ℂ} (h : 1 / 2 < ρ.re) :
    ∫ x : ℝ, ‖HR18_e ρ x‖ ^ 2 = 1 / (2 * ρ.re - 1) := by
  simp_rw [HR18_norm_sq]
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith))]
  have hpos : 0 < 2 * (ρ.re - 1) + 1 := by linarith
  rw [Real.one_rpow, Real.zero_rpow hpos.ne']
  congr 1 <;> ring

/-! ## #23 Riemann split -/

/-- **#23.** If `F` is invariant under `x ↦ x⁻¹ F(x⁻¹)` and the Mellin integral of `F` at `s`
converges absolutely, then `M_F(s) = A(s) + A(1 − s)` where `A(s) = ∫_1^∞ x^{s−1} F(x) dx`. -/
theorem HR21_riemann_split (F : ℝ → ℂ) (s : ℂ)
    (hJ : ∀ x : ℝ, 0 < x → ((x⁻¹ : ℝ) : ℂ) * F x⁻¹ = F x)
    (hM : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * F x) (Ioi 0)) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ (s - 1) * F x
      = (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * F x)
        + ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((1 - s) - 1) * F x := by
  set f : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * F x with hf
  have hsplit : ∫ x in Ioi (0 : ℝ), f x = (∫ x in Ioc (0 : ℝ) 1, f x) + ∫ x in Ioi (1 : ℝ), f x := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1)]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hM.mono_set Set.Ioc_subset_Ioi_self) (hM.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hinv : ∫ x in Ioc (0 : ℝ) 1, f x = ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((1 - s) - 1) * F x := by
    rw [integral_Ioc_eq_integral_Ioo]
    have himg : (fun x : ℝ => x⁻¹) '' Ioi (1 : ℝ) = Ioo 0 1 := by
      rw [Set.image_inv_eq_inv, inv_Ioi₀ zero_lt_one, inv_one]
    have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioi (1 : ℝ))
      (f := fun x : ℝ => x⁻¹) (f' := fun x : ℝ => -(x ^ 2)⁻¹) measurableSet_Ioi
      (fun x hx => (hasDerivAt_inv (lt_trans zero_lt_one hx).ne').hasDerivWithinAt)
      (fun x hx y hy h => by simpa using h) f
    rw [himg] at hcv
    rw [hcv]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    simp only [hf, abs_neg, abs_of_pos (inv_pos.mpr (pow_pos hy0 2)), Complex.real_smul]
    have hFy : F y⁻¹ = (y : ℂ) * F y := by
      have := hJ y hy0
      have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
      rw [← this]; push_cast; field_simp
    rw [hFy]
    have hc : ((y⁻¹ : ℝ) : ℂ) ^ (s - 1) = ((y : ℂ) ^ (s - 1))⁻¹ := by
      rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg hy0.le]; exact Real.pi_ne_zero.symm)]
    rw [hc]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
    have ha : (y : ℂ) ^ (s - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    have e1 : (y : ℂ) ^ ((1 - s) - 1) = ((y : ℂ) ^ (s - 1))⁻¹ * (y : ℂ)⁻¹ := by
      rw [show (1 - s) - 1 = -(s - 1) - 1 by ring, Complex.cpow_sub _ _ hy', Complex.cpow_neg,
        Complex.cpow_one, div_eq_mul_inv]
    rw [e1]
    push_cast
    field_simp
  rw [hsplit, hinv]
  exact add_comm _ _

/-- **#23 (real `F`, critical line).** If `F` is real-valued with `x⁻¹ F(x⁻¹) = F(x)` and its
Mellin integral at `s = 1/2 + i t` converges absolutely, then `M_F(s) = 2 Re A(s)` (in particular
`M_F(s)` is real), where `A(s) = ∫_1^∞ x^{s−1} F(x) dx`. -/
theorem HR21_riemann_split_critical (F : ℝ → ℝ) (t : ℝ)
    (hJ : ∀ x : ℝ, 0 < x → x⁻¹ * F x⁻¹ = F x)
    (hM : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ))
      (Ioi 0)) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ)
      = ((2 * (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ)).re
          : ℝ) : ℂ) := by
  set s : ℂ := (1 / 2 : ℂ) + t * Complex.I with hs
  have hsplit := HR21_riemann_split (fun x => (F x : ℂ)) s
    (fun x hx => by exact_mod_cast hJ x hx) hM
  rw [hsplit]
  have hconj : (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((1 - s) - 1) * (F x : ℂ))
      = conj (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (F x : ℂ)) := by
    rw [← integral_conj]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    have harg : (x : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_ne_zero.symm
    have h1 : (1 - s) - 1 = conj (s - 1) := by
      rw [hs]
      apply Complex.ext <;> simp; ring
    rw [map_mul, Complex.conj_ofReal, h1, Complex.cpow_conj _ _ harg, Complex.conj_ofReal]
  rw [hconj]
  have := Complex.add_conj (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (s - 1) * (F x : ℂ))
  rw [this]

/-- **#23 (zeros).** In that situation, `M_F(1/2 + i t) = 0` iff `Re A(1/2 + i t) = 0`. -/
theorem HR21_riemann_split_critical_zero_iff (F : ℝ → ℝ) (t : ℝ)
    (hJ : ∀ x : ℝ, 0 < x → x⁻¹ * F x⁻¹ = F x)
    (hM : IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ))
      (Ioi 0)) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ)) = 0 ↔
      (∫ x in Ioi (1 : ℝ), (x : ℂ) ^ ((1 / 2 : ℂ) + t * Complex.I - 1) * (F x : ℂ)).re = 0 := by
  rw [HR21_riemann_split_critical F t hJ hM]
  simp

/-! ## #24 The lattice state is negative on `[1, ∞)` -/

/-- `θ₊(y) = Σ_{n ≥ 1} e^{−π n² y}`. -/
noncomputable def HR_thetaPlus (y : ℝ) : ℝ :=
  ∑' n : ℕ, Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ)) ^ 2 * y)

/-- `F_ζ(x) = θ₊(x²) − 1/(2x)`. -/
noncomputable def HR_latticeState (x : ℝ) : ℝ := HR_thetaPlus (x ^ 2) - 1 / (2 * x)

private theorem HR_theta_summable {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ)) ^ 2 * y) := by
  have hg : Summable fun n : ℕ => Real.exp (-Real.pi * y) ^ (n + 1) := by
    have h0 : Real.exp (-Real.pi * y) < 1 := by
      have : Real.exp (-Real.pi * y) < Real.exp 0 :=
        Real.exp_lt_exp.mpr (by nlinarith [mul_pos Real.pi_pos hy])
      simpa using this
    exact (summable_geometric_of_lt_one (Real.exp_pos _).le h0).comp_injective
      (add_left_injective 1)
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_) hg
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  push_cast
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpos : 0 ≤ Real.pi * y * ((n : ℝ) + 1) * n :=
    mul_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le hy.le) (by linarith)) hn0
  nlinarith [hpos]

/-- **#24 (key estimate).** `θ₊(1) < 1/2`. -/
theorem HR_thetaPlus_one_lt_half : HR_thetaPlus 1 < 1 / 2 := by
  have hq : Real.exp (-Real.pi) < 1 / 3 := by
    have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have : (3 : ℝ) < Real.exp Real.pi := by
      calc (3 : ℝ) < 1 + Real.pi := by linarith
        _ ≤ Real.exp Real.pi := by linarith [Real.add_one_le_exp Real.pi]
    rw [Real.exp_neg]
    rw [inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    simpa using this
  have hq0 : 0 < Real.exp (-Real.pi) := Real.exp_pos _
  have hg : Summable fun n : ℕ => Real.exp (-Real.pi) ^ (n + 1) :=
    (summable_geometric_of_lt_one hq0.le (by linarith)).comp_injective (add_left_injective 1)
  have hle : HR_thetaPlus 1 ≤ ∑' n : ℕ, Real.exp (-Real.pi) ^ (n + 1) := by
    refine Summable.tsum_le_tsum (fun n => ?_) (HR_theta_summable one_pos) hg
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : 0 ≤ Real.pi * ((n : ℝ) + 1) * n :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) hn0
    nlinarith [hpos]
  have hsum : ∑' n : ℕ, Real.exp (-Real.pi) ^ (n + 1)
      = Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi)) := by
    simp_rw [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hq0.le (by linarith)]
    field_simp
  rw [hsum] at hle
  have h1 : Real.exp (-Real.pi) / (1 - Real.exp (-Real.pi)) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]; linarith
  linarith

/-- For `x ≥ 1`, `x · θ₊(x²) ≤ θ₊(1)`. -/
theorem HR_x_thetaPlus_le {x : ℝ} (hx : 1 ≤ x) : x * HR_thetaPlus (x ^ 2) ≤ HR_thetaPlus 1 := by
  have hx0 : 0 < x := by linarith
  unfold HR_thetaPlus
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_) ((HR_theta_summable (by positivity)).mul_left x)
    (HR_theta_summable one_pos)
  -- x e^{−π m² x²} ≤ e^{−π m²}, with m = n + 1 ≥ 1
  set m : ℝ := (((n + 1 : ℕ) : ℝ)) with hm
  have hm1 : (1 : ℝ) ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hkey : x ≤ Real.exp (Real.pi * m ^ 2 * (x ^ 2 - 1)) := by
    have h1 : 1 + Real.pi * m ^ 2 * (x ^ 2 - 1) ≤ Real.exp (Real.pi * m ^ 2 * (x ^ 2 - 1)) := by
      simpa [add_comm] using Real.add_one_le_exp (Real.pi * m ^ 2 * (x ^ 2 - 1))
    have h2 : x ≤ 1 + Real.pi * m ^ 2 * (x ^ 2 - 1) := by
      have hx2 : 0 ≤ x ^ 2 - 1 := by nlinarith
      have hpm : 1 ≤ Real.pi * m ^ 2 := by nlinarith [Real.pi_gt_three, sq_nonneg m]
      nlinarith [mul_nonneg hx2 (sub_nonneg.mpr hpm)]
    linarith
  calc x * Real.exp (-Real.pi * m ^ 2 * x ^ 2)
      ≤ Real.exp (Real.pi * m ^ 2 * (x ^ 2 - 1)) * Real.exp (-Real.pi * m ^ 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le
    _ = Real.exp (-Real.pi * m ^ 2 * 1) := by
        rw [← Real.exp_add]; congr 1; ring

/-- **#24.** `F_ζ(x) < 0` for `x ≥ 1`. -/
theorem HR21_lattice_state_negative_right {x : ℝ} (hx : 1 ≤ x) : HR_latticeState x < 0 := by
  have hx0 : 0 < x := by linarith
  have h := HR_x_thetaPlus_le hx
  have h2 := HR_thetaPlus_one_lt_half
  unfold HR_latticeState
  have : HR_thetaPlus (x ^ 2) < 1 / (2 * x) := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- `φ(u) = e^{u/2} F_ζ(e^u)`, the lattice state in logarithmic coordinates. -/
noncomputable def HR_phi (u : ℝ) : ℝ := Real.exp (u / 2) * HR_latticeState (Real.exp u)

/-- **#24 (log coordinates).** `φ(u) < 0` for `u ≥ 0` (in particular on `(0, ∞)`). -/
theorem HR21_phi_negative {u : ℝ} (hu : 0 ≤ u) : HR_phi u < 0 :=
  mul_neg_of_pos_of_neg (Real.exp_pos _) (HR21_lattice_state_negative_right (Real.one_le_exp hu))

/-- **#24 (Hankel form).** For measurable `f ≥ 0` supported-positively on a set of positive measure
in `(0,∞)`, and with integrable integrand, the cross-boundary Hankel form
`∫∫ f(u) φ(u+v) f(v) du dv` over `(0,∞)²` is strictly negative. -/
theorem HR21_hankel_form_negative (f : ℝ → ℝ) (hf0 : ∀ u, 0 ≤ f u) (hfm : Measurable f)
    (hint : Integrable (fun p : ℝ × ℝ => f p.1 * HR_phi (p.1 + p.2) * f p.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (hpos : 0 < volume (Ioi (0 : ℝ) ∩ {u | 0 < f u})) :
    ∫ p : ℝ × ℝ, f p.1 * HR_phi (p.1 + p.2) * f p.2
      ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) < 0 := by
  set μ := (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))) with hμ
  set g : ℝ × ℝ → ℝ := fun p => f p.1 * HR_phi (p.1 + p.2) * f p.2 with hg
  have hμ' : μ = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    rw [hμ, Measure.prod_restrict]
  have hmeas : MeasurableSet (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    measurableSet_Ioi.prod measurableSet_Ioi
  have hneg : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), g p ≤ 0 := by
    intro p hp
    have hφ : HR_phi (p.1 + p.2) < 0 := HR21_phi_negative (by
      have := hp.1; have := hp.2; simp only [Set.mem_Ioi] at *; linarith)
    simp only [hg]
    have := hf0 p.1; have := hf0 p.2
    nlinarith [mul_nonneg (hf0 p.1) (hf0 p.2)]
  have hae : 0 ≤ᵐ[μ] fun p => -g p := by
    rw [hμ', Filter.EventuallyLE, ae_restrict_iff' hmeas]
    exact Filter.Eventually.of_forall fun p hp => by simpa using hneg p hp
  have hTmeas : MeasurableSet (Ioi (0 : ℝ) ∩ {u : ℝ | 0 < f u}) :=
    measurableSet_Ioi.inter (measurableSet_lt measurable_const hfm)
  have hS : 0 < (volume.restrict (Ioi (0 : ℝ))) (Ioi (0 : ℝ) ∩ {u : ℝ | 0 < f u}) := by
    rw [Measure.restrict_apply hTmeas, Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hpos
  have hsupp : 0 < μ (Function.support fun p => -g p) := by
    have hsub : (Ioi (0 : ℝ) ∩ {u : ℝ | 0 < f u}) ×ˢ (Ioi (0 : ℝ) ∩ {u : ℝ | 0 < f u})
        ⊆ Function.support fun p => -g p := by
      rintro ⟨a, b⟩ ⟨⟨ha0, haf⟩, ⟨hb0, hbf⟩⟩
      have hφ : HR_phi (a + b) < 0 := HR21_phi_negative (by
        simp only [Set.mem_Ioi] at ha0 hb0; linarith)
      have haf' : 0 < f a := haf
      have hbf' : 0 < f b := hbf
      have : g (a, b) < 0 := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg haf' hφ) hbf'
      exact neg_ne_zero.mpr this.ne
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [hμ, Measure.prod_prod]
    exact ENNReal.mul_pos hS.ne' hS.ne'
  have hpos' : 0 < ∫ p, -g p ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hae hint.neg).mpr hsupp
  rw [integral_neg] at hpos'
  linarith

/-! ## #22 Mellin convolution acts diagonally on power functions -/

/-- **#22.** For every `F` (no hypothesis is needed: the substitution `w = x/y` preserves the
measure `dy/y`), the Mellin convolution `(Tf)(x) = ∫_0^∞ F(x/y) f(y) dy/y` of `f(y) = y^{-s}`
equals `x^{-s} · M_F(s)` with `M_F(s) = ∫_0^∞ w^{s-1} F(w) dw`. -/
theorem HR21_mellin_convolution_diagonal (F : ℝ → ℂ) (s : ℂ) {x : ℝ} (hx : 0 < x) :
    ∫ y in Ioi (0 : ℝ), F (x / y) * (y : ℂ) ^ (-s) / (y : ℂ)
      = (x : ℂ) ^ (-s) * ∫ w in Ioi (0 : ℝ), (w : ℂ) ^ (s - 1) * F w := by
  have himg : (fun y : ℝ => x / y) '' Ioi (0 : ℝ) = Ioi 0 := by
    ext w
    simp only [Set.mem_image, Set.mem_Ioi]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact div_pos hx hy
    · intro hw; exact ⟨x / w, div_pos hx hw, by field_simp⟩
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun y : ℝ => x / y) (f' := fun y : ℝ => -(x / y ^ 2)) measurableSet_Ioi
    (fun y hy => by
      have hy0 : y ≠ 0 := (Set.mem_Ioi.mp hy).ne'
      exact (((hasDerivAt_const y x).div (hasDerivAt_id' y) hy0).congr_deriv
        (by ring)).hasDerivWithinAt)
    (fun y hy z hz h => by
      have hy0 : y ≠ 0 := (Set.mem_Ioi.mp hy).ne'
      have hz0 : z ≠ 0 := (Set.mem_Ioi.mp hz).ne'
      simp only at h
      field_simp at h
      linarith [h]) (fun w : ℝ => (w : ℂ) ^ (s - 1) * F w)
  rw [himg] at hcv
  rw [hcv, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
  have hy0 : (0 : ℝ) < y := hy
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  simp only [abs_neg, abs_of_pos (div_pos hx (pow_pos hy0 2)), Complex.real_smul]
  have hdiv : ((x / y : ℝ) : ℂ) ^ (s - 1) = (x : ℂ) ^ (s - 1) * ((y : ℂ) ^ (s - 1))⁻¹ := by
    rw [div_eq_mul_inv, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le
      (inv_nonneg.mpr hy0.le), Complex.ofReal_inv, Complex.inv_cpow _ _ (by
        rw [Complex.arg_ofReal_of_nonneg hy0.le]; exact Real.pi_ne_zero.symm)]
  rw [hdiv]
  have hxs : (x : ℂ) ^ (s - 1) = (x : ℂ) ^ s / (x : ℂ) := by
    rw [Complex.cpow_sub _ _ hxc, Complex.cpow_one]
  have hys : (y : ℂ) ^ (s - 1) = (y : ℂ) ^ s / (y : ℂ) := by
    rw [Complex.cpow_sub _ _ hyc, Complex.cpow_one]
  have hmx : (x : ℂ) ^ (-s) = ((x : ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
  have hmy : (y : ℂ) ^ (-s) = ((y : ℂ) ^ s)⁻¹ := Complex.cpow_neg _ _
  have hxs0 : (x : ℂ) ^ s ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hys0 : (y : ℂ) ^ s ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  rw [hxs, hys, hmx, hmy]
  push_cast
  field_simp

/-! ## #13 The lattice state is shadow-invariant -/

open UpperHalfPlane in
/-- The real-variable theta functional equation, `1 + 2θ₊(1/y) = √y (1 + 2θ₊(y))`, from
Mathlib's `jacobiTheta_S_smul`. -/
theorem HR_theta_functional_equation {y : ℝ} (hy : 0 < y) :
    1 + 2 * HR_thetaPlus (1 / y) = Real.sqrt y * (1 + 2 * HR_thetaPlus y) := by
  let τ : ℍ := ⟨Complex.I * y, by simpa using hy⟩
  have hτ : (τ : ℂ) = Complex.I * y := rfl
  have hS : ((ModularGroup.S • τ : ℍ) : ℂ) = Complex.I * ((1 / y : ℝ) : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp only [hτ]
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
    push_cast
    field_simp
    simp [Complex.I_sq]
  have h := jacobiTheta_S_smul τ
  rw [hS, hτ] at h
  have hsqrt : (-Complex.I * (Complex.I * (y : ℂ))) ^ (1 / 2 : ℂ) = ((Real.sqrt y : ℝ) : ℂ) := by
    have : -Complex.I * (Complex.I * (y : ℂ)) = (y : ℂ) := by
      simp [← mul_assoc, Complex.I_mul_I]
    rw [this, Real.sqrt_eq_rpow, Complex.ofReal_cpow hy.le]
    norm_num
  rw [hsqrt] at h
  have htheta : ∀ z : ℝ, 0 < z → jacobiTheta (Complex.I * (z : ℂ))
      = ((1 + 2 * HR_thetaPlus z : ℝ) : ℂ) := by
    intro z hz
    rw [jacobiTheta_eq_tsum_nat (by simpa using hz)]
    unfold HR_thetaPlus
    rw [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_tsum]
    congr 2
    refine tsum_congr fun n => ?_
    rw [Complex.ofReal_exp]
    congr 1
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    push_cast
    linear_combination ((Real.pi : ℂ) * ((n : ℂ) + 1) ^ 2 * (z : ℂ)) * hI
  rw [htheta _ (by positivity), htheta y hy] at h
  exact_mod_cast h

/-- **#13.** `x⁻¹ F_ζ(1/x) = F_ζ(x)` for `x > 0`. -/
theorem HR19_lattice_state_shadow_invariant {x : ℝ} (hx : 0 < x) :
    x⁻¹ * HR_latticeState (1 / x) = HR_latticeState x := by
  have hfe := HR_theta_functional_equation (y := x ^ 2) (by positivity)
  have hsq : Real.sqrt (x ^ 2) = x := Real.sqrt_sq hx.le
  rw [hsq] at hfe
  have h1 : (1 / x) ^ 2 = 1 / x ^ 2 := by rw [one_div, one_div, inv_pow]
  unfold HR_latticeState
  rw [h1]
  field_simp
  linarith

end GppHeartMellin

#print axioms GppHeartMellin.HR18_truncated_primary_L2_iff
#print axioms GppHeartMellin.HR18_truncated_primary_norm_sq
#print axioms GppHeartMellin.HR21_riemann_split
#print axioms GppHeartMellin.HR21_riemann_split_critical
#print axioms GppHeartMellin.HR21_riemann_split_critical_zero_iff
#print axioms GppHeartMellin.HR_thetaPlus_one_lt_half
#print axioms GppHeartMellin.HR_x_thetaPlus_le
#print axioms GppHeartMellin.HR21_lattice_state_negative_right
#print axioms GppHeartMellin.HR21_phi_negative
#print axioms GppHeartMellin.HR21_hankel_form_negative
#print axioms GppHeartMellin.HR21_mellin_convolution_diagonal
#print axioms GppHeartMellin.HR_theta_functional_equation
#print axioms GppHeartMellin.HR19_lattice_state_shadow_invariant
