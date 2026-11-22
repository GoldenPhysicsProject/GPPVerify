/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude; statement from Codex / GPT, audited by Turbo)
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GppVerify.RiemannHypothesis.CausalKernels
import GppVerify.RiemannHypothesis.CausalTailEstimate
import GppVerify.RiemannHypothesis.CausalAbel

/-!
# Norm bounds for the causal kernels (Part D2 of the causal proof of `EnergyZeroInequality`)

**Unconditional; this is a lemma, not RH.** Part D2 of the four-part formalization of Codex's causal
proof (`causal_zero_bound.md` §3, GPPDiscovery2 `cae0656`, Turbo-audited), on top of the Abel-summation
formulas of Part D1 (`GppCausalAbel.Z_formula`, `kk_formula`).

Main results, on `(0, ∞)` and in the real-integral form that `GppCausalTail.causal_tail_estimate`
(Part A) consumes:

* `w_sq_bound`: `w² ∈ L¹(0,∞)`, `∫ w² ≤ (5/2)²`;
* `Z_sq_bound`: `Z² ∈ L¹(0,∞)`, `∫ Z² ≤ 9²`;
* `kk_L1_bound`: `k ∈ L¹(0,∞)`, `∫ |k| ≤ 18`;
* `hh_sq_bound c`: `h = w − cZ`, `∫ h² ≤ (5/2 + 9|c|)²`.

Also `measurable_Z`, `measurable_kk`, `measurable_hh` (genuine measurability, which Part A's statement
asks for).

Route (as in §3 of the note): `g_j ≥ 0`, `g_j ≤ 1`, `∫ g_j = 1` (via `Γ`), so `‖g_j‖₁ = 1` and
`‖g_j‖₂ ≤ 1`; `‖f‖₁ ≤ 2` for `f(u) = e^{−u/2}{e^u}`; Young `L¹ ∗ L² → L²` (`eLpNorm_rconv_two_le`,
from Part A's `lintegral_sq_conv_le`) and `L¹ ∗ L¹ → L¹` (`eLpNorm_rconv_one_le`, by Tonelli); then the
triangle inequality (`eLpNorm_comb2_le`) on the D1 formulas:
`‖Z‖₂ ≤ 3/2 + 2·(1 + 2 + 3/4) = 9`, `‖w‖₂ ≤ 5/2`, `‖k‖₁ ≤ 3 + 2·(1 + 3 + 11/4 + 3/4) = 18`.

**Not in this file:** Part C (transforms at a zero, continuation to `Re s > 0`) and the final assembly
`energyZeroInequality_causal`.
-/

open MeasureTheory Set GppCausalKernels GppCausalAbel ENNReal

namespace GppCausalNorms

theorem integral_g (j : ℕ) (hj : 1 ≤ j) : ∫ t in Ioi (0:ℝ), g j t = 1 := by
  have h1 : ∀ t ∈ Ioi (0:ℝ), g j t = Real.exp (-t) * t ^ ((j : ℝ) - 1) / ((j - 1).factorial : ℝ) := by
    intro t ht
    have : 0 ≤ t := le_of_lt ht
    simp only [g, if_pos this]
    congr 2
    rw [← Real.rpow_natCast]
    congr 1
    push_cast [Nat.cast_sub hj]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi h1]
  rw [integral_div, ← Real.Gamma_eq_integral (by exact_mod_cast hj)]
  have : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by push_cast [Nat.cast_sub hj]; ring
  rw [this, Real.Gamma_nat_eq_factorial]
  have : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  field_simp


theorem g_nonneg (j : ℕ) (t : ℝ) : 0 ≤ g j t := by
  unfold g; split_ifs with h
  · positivity
  · exact le_rfl

theorem g_le_one {j : ℕ} (t : ℝ) : g j t ≤ 1 := by
  unfold g; split_ifs with h
  · have := Real.pow_div_factorial_le_exp t h (j - 1)
    have hp : 0 < Real.exp t := Real.exp_pos t
    calc Real.exp (-t) * t ^ (j - 1) / ((j - 1).factorial : ℝ)
        = Real.exp (-t) * (t ^ (j - 1) / ((j - 1).factorial : ℝ)) := by ring
      _ ≤ Real.exp (-t) * Real.exp t := by gcongr
      _ = 1 := by rw [← Real.exp_add]; simp
  · exact zero_le_one

theorem g_of_neg {j : ℕ} {t : ℝ} (ht : t < 0) : g j t = 0 := by simp [g, not_le.2 ht]

theorem measurable_g (j : ℕ) : Measurable (g j) := by
  unfold g
  refine Measurable.ite measurableSet_Ici ?_ measurable_const
  fun_prop

theorem integrableOn_g {j : ℕ} (hj : 1 ≤ j) : IntegrableOn (g j) (Ioi (0:ℝ)) := by
  by_contra h
  have := integral_g j hj
  rw [integral_undef h] at this
  exact zero_ne_one this


/-- A function vanishing on `t < 0` has the same lower integral over `ℝ` as over `(0, ∞)`. -/
theorem lintegral_causal (G : ℝ → ℝ≥0∞) (hG : ∀ t < 0, G t = 0) :
    ∫⁻ t, G t = ∫⁻ t in Ioi (0:ℝ), G t := by
  rw [← lintegral_add_compl G (measurableSet_Ioi (a := (0:ℝ)))]
  have : ∫⁻ t in (Ioi (0:ℝ))ᶜ, G t = 0 := by
    rw [compl_Ioi, setLIntegral_congr Iio_ae_eq_Iic.symm]
    rw [setLIntegral_congr_fun measurableSet_Iio (g := fun _ => 0) (fun t ht => hG t ht)]
    simp
  rw [this, add_zero]

theorem enorm_g (j : ℕ) (t : ℝ) : ‖g j t‖ₑ = ENNReal.ofReal (g j t) := by
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (g_nonneg j t)]

theorem eLpNorm_g_one {j : ℕ} (hj : 1 ≤ j) : eLpNorm (g j) 1 volume = 1 := by
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_causal _ (fun t ht => by simp [g_of_neg ht])]
  simp_rw [enorm_g]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_g hj)
    (Filter.Eventually.of_forall fun t => g_nonneg j t), integral_g j hj]
  simp

theorem eLpNorm_g_two_le {j : ℕ} (hj : 1 ≤ j) : eLpNorm (g j) 2 volume ≤ 1 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h1 : ∫⁻ t, ‖g j t‖ₑ ^ (ENNReal.toReal 2) ≤ 1 := by
    have : ∀ t, ‖g j t‖ₑ ^ (ENNReal.toReal 2) ≤ ‖g j t‖ₑ := by
      intro t
      have hle : ‖g j t‖ₑ ≤ 1 := by
        rw [enorm_g]; exact ENNReal.ofReal_le_one.2 (g_le_one t)
      have : ENNReal.toReal 2 = ((2:ℕ) : ℝ) := by simp
      rw [this, ENNReal.rpow_natCast]
      calc ‖g j t‖ₑ ^ 2 = ‖g j t‖ₑ * ‖g j t‖ₑ := by ring
        _ ≤ ‖g j t‖ₑ * 1 := by gcongr
        _ = _ := mul_one _
    calc ∫⁻ t, ‖g j t‖ₑ ^ (ENNReal.toReal 2) ≤ ∫⁻ t, ‖g j t‖ₑ := lintegral_mono this
      _ = eLpNorm (g j) 1 volume := eLpNorm_one_eq_lintegral_enorm.symm
      _ = 1 := eLpNorm_g_one hj
  calc (∫⁻ t, ‖g j t‖ₑ ^ (ENNReal.toReal 2)) ^ (1 / ENNReal.toReal 2) ≤ 1 ^ (1 / ENNReal.toReal 2) := by
        gcongr
    _ = 1 := by simp


theorem eLpNorm_two_eq' (f : ℝ → ℝ) :
    eLpNorm f 2 volume = (∫⁻ t, ‖f t‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have e2 : ENNReal.toReal 2 = ((2:ℕ) : ℝ) := by simp
  simp only [e2, ENNReal.rpow_natCast]
  norm_num

/-- Young `L¹ ∗ L² → L²` in `eLpNorm` form, for the real convolution `rconv`. -/
theorem eLpNorm_rconv_two_le (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) :
    eLpNorm (GppCausalTail.rconv k f) 2 volume ≤ eLpNorm k 1 volume * eLpNorm f 2 volume := by
  have h := GppCausalTail.lintegral_sq_rconv_le k f hk hf
  rw [eLpNorm_two_eq', eLpNorm_two_eq', eLpNorm_one_eq_lintegral_enorm]
  calc (∫⁻ t, ‖GppCausalTail.rconv k f t‖ₑ ^ 2) ^ (1 / 2 : ℝ)
      ≤ ((∫⁻ s, ‖k s‖ₑ) ^ 2 * ∫⁻ t, ‖f t‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by gcongr
    _ = (∫⁻ s, ‖k s‖ₑ) * (∫⁻ t, ‖f t‖ₑ ^ 2) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
          ← ENNReal.rpow_mul]
        norm_num

/-- `L¹ ∗ L¹ → L¹` in `eLpNorm` form. -/
theorem eLpNorm_rconv_one_le (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) :
    eLpNorm (GppCausalTail.rconv k f) 1 volume ≤ eLpNorm k 1 volume * eLpNorm f 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm]
  have hpt : ∀ t, ‖GppCausalTail.rconv k f t‖ₑ ≤ ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ := by
    intro t
    rw [GppCausalTail.rconv_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    simp [enorm_mul]
  have hG : Measurable (fun p : ℝ × ℝ => ‖k p.2‖ₑ * ‖f (p.1 - p.2)‖ₑ) :=
    ((hk.comp measurable_snd).enorm).mul ((hf.comp (measurable_fst.sub measurable_snd)).enorm)
  calc ∫⁻ t, ‖GppCausalTail.rconv k f t‖ₑ ≤ ∫⁻ t, ∫⁻ s, ‖k s‖ₑ * ‖f (t - s)‖ₑ := lintegral_mono hpt
    _ = ∫⁻ s, ∫⁻ t, ‖k s‖ₑ * ‖f (t - s)‖ₑ := lintegral_lintegral_swap hG.aemeasurable
    _ = ∫⁻ s, ‖k s‖ₑ * ∫⁻ t, ‖f t‖ₑ := by
        refine lintegral_congr fun s => ?_
        have hm : Measurable (fun t : ℝ => ‖f (t - s)‖ₑ) := (hf.comp (measurable_id.sub measurable_const)).enorm
        rw [lintegral_const_mul _ hm, lintegral_sub_right_eq_self (fun t => ‖f t‖ₑ) s]
    _ = (∫⁻ s, ‖k s‖ₑ) * ∫⁻ t, ‖f t‖ₑ := by
        rw [lintegral_mul_const _ hk.enorm]


/-- `eLpNorm` of a real multiple. -/
theorem eLpNorm_mul_const' (α : ℝ) (a : ℝ → ℝ) (p : ℝ≥0∞) (μ : Measure ℝ) :
    eLpNorm (fun t => α * a t) p μ = ENNReal.ofReal |α| * eLpNorm a p μ := by
  rw [show (fun t => α * a t) = α • a from rfl, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]

/-- Triangle inequality for a two-term real combination. -/
theorem eLpNorm_comb2 {p : ℝ≥0∞} (hp : 1 ≤ p) (μ : Measure ℝ) (a b : ℝ → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (α β : ℝ) :
    eLpNorm (fun t => α * a t + β * b t) p μ ≤
      ENNReal.ofReal |α| * eLpNorm a p μ + ENNReal.ofReal |β| * eLpNorm b p μ := by
  have h := eLpNorm_add_le (f := fun t => α * a t) (g := fun t => β * b t) (μ := μ)
    (ha.const_mul α) (hb.const_mul β) hp
  rw [eLpNorm_mul_const', eLpNorm_mul_const'] at h
  exact h


theorem measurable_ff : Measurable ff := by
  unfold ff
  exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).mul
    (measurable_fract.comp Real.measurable_exp)

theorem ff_nonneg (u : ℝ) : 0 ≤ ff u := by
  unfold ff; exact mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)

theorem ff_le (u : ℝ) : ff u ≤ Real.exp (-u / 2) := by
  unfold ff
  calc Real.exp (-u / 2) * Int.fract (Real.exp u) ≤ Real.exp (-u / 2) * 1 := by
        gcongr; exact (Int.fract_lt_one _).le
    _ = _ := mul_one _

/-- The causal truncation of `ff`. -/
noncomputable def ff0 : ℝ → ℝ := (Ioi (0:ℝ)).indicator ff

theorem measurable_ff0 : Measurable ff0 := measurable_ff.indicator measurableSet_Ioi

theorem eLpNorm_ff0_le : eLpNorm ff0 1 volume ≤ ENNReal.ofReal 2 := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  have h1 : ∀ u, ‖ff0 u‖ₑ = (Ioi (0:ℝ)).indicator (fun u => ENNReal.ofReal (ff u)) u := by
    intro u
    by_cases hu : u ∈ Ioi (0:ℝ)
    · simp only [ff0, indicator_of_mem hu]
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (ff_nonneg u)]
    · simp [ff0, indicator_of_notMem hu]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ioi]
  have hint : IntegrableOn (fun u : ℝ => Real.exp ((-(1/2:ℝ)) * u)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  calc ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (ff u)
      ≤ ∫⁻ u in Ioi (0:ℝ), ENNReal.ofReal (Real.exp ((-(1/2:ℝ)) * u)) := by
        refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
        refine (ff_le u).trans (le_of_eq ?_)
        congr 1; ring
    _ = ENNReal.ofReal (∫ u in Ioi (0:ℝ), Real.exp ((-(1/2:ℝ)) * u)) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)).symm
    _ = ENNReal.ofReal 2 := by
        rw [integral_exp_mul_Ioi (by norm_num)]
        congr 1; norm_num

/-- For `G` vanishing on `(−∞, 0)`, `(ff0 ⋆ G)(t) = ∫_{(0,t]} ff(u) G(t−u) du`. -/
theorem rconv_ff0_eq {G : ℝ → ℝ} (hG : ∀ x, x < 0 → G x = 0) (t : ℝ) :
    GppCausalTail.rconv ff0 G t = ∫ u in Ioc (0:ℝ) t, ff u * G (t - u) := by
  rw [GppCausalTail.rconv_apply, ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  by_cases hs : s ∈ Ioc (0:ℝ) t
  · simp [ff0, indicator_of_mem hs, indicator_of_mem (show s ∈ Ioi (0:ℝ) from hs.1)]
  · rw [indicator_of_notMem hs]
    by_cases h0 : s ≤ 0
    · simp [ff0, indicator_of_notMem (show s ∉ Ioi (0:ℝ) by simpa using h0)]
    · have : t < s := by
        by_contra h; exact hs ⟨not_le.1 h0, not_lt.1 h⟩
      simp [hG (t - s) (by linarith)]


theorem eLpNorm_comb2_le {p : ℝ≥0∞} (hp : 1 ≤ p) (μ : Measure ℝ) (a b : ℝ → ℝ)
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) (α β c₁ c₂ : ℝ)
    (h1 : eLpNorm a p μ ≤ ENNReal.ofReal c₁) (h2 : eLpNorm b p μ ≤ ENNReal.ofReal c₂)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    eLpNorm (fun t => α * a t + β * b t) p μ ≤ ENNReal.ofReal (|α| * c₁ + |β| * c₂) := by
  refine (eLpNorm_comb2 hp μ a b ha hb α β).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.ofReal_mul (abs_nonneg _)]
  gcongr

/-- Linear combinations of the kernels, in the shape produced by `eLpNorm_comb2_le`. -/
noncomputable def u1g (t : ℝ) : ℝ := 1 * (1 * g 2 t + (-2) * g 3 t) + (3 / 4) * g 4 t
noncomputable def u2g (t : ℝ) : ℝ :=
  1 * (1 * (1 * g 1 t + (-3) * g 2 t) + (11 / 4) * g 3 t) + (-3 / 4) * g 4 t
noncomputable def Gz (t : ℝ) : ℝ := 1 * g 3 t + (-1 / 2) * g 4 t
noncomputable def Gk (t : ℝ) : ℝ := 1 * (1 * g 2 t + (-3 / 2) * g 3 t) + (1 / 2) * g 4 t
noncomputable def wg (t : ℝ) : ℝ := 1 * g 3 t + (-3 / 2) * g 4 t

theorem wg_eq (t : ℝ) : wg t = w t := by simp only [wg, w]; ring

theorem aesm_g (j : ℕ) (μ : Measure ℝ) : AEStronglyMeasurable (g j) μ :=
  (measurable_g j).aestronglyMeasurable

theorem eLpNorm_u1g : eLpNorm u1g 2 volume ≤ ENNReal.ofReal (15 / 4) := by
  have h12 : eLpNorm (fun t => 1 * g 2 t + (-2) * g 3 t) 2 volume ≤ ENNReal.ofReal (|1| * 1 + |-2| * 1) :=
    eLpNorm_comb2_le (by norm_num) volume _ _ (aesm_g 2 _) (aesm_g 3 _) 1 (-2) 1 1
      (by simpa using eLpNorm_g_two_le (by norm_num : 1 ≤ 2)) (by simpa using eLpNorm_g_two_le (by norm_num : 1 ≤ 3))
      (by norm_num) (by norm_num)
  have := eLpNorm_comb2_le (by norm_num) volume (fun t => 1 * g 2 t + (-2) * g 3 t) (g 4)
    (((aesm_g 2 _).const_mul 1).add ((aesm_g 3 _).const_mul (-2))) (aesm_g 4 _) 1 (3 / 4) _ 1 h12
    (by simpa using eLpNorm_g_two_le (by norm_num : 1 ≤ 4)) (by norm_num) (by norm_num)
  refine this.trans (le_of_eq ?_)
  congr 1; norm_num


theorem eLpNorm_g_two_le' {j : ℕ} (hj : 1 ≤ j) : eLpNorm (g j) 2 volume ≤ ENNReal.ofReal 1 := by
  rw [ENNReal.ofReal_one]; exact eLpNorm_g_two_le hj

theorem eLpNorm_g_one_le {j : ℕ} (hj : 1 ≤ j) : eLpNorm (g j) 1 volume ≤ ENNReal.ofReal 1 := by
  rw [eLpNorm_g_one hj]; simp

theorem eLpNorm_Gz : eLpNorm Gz 2 volume ≤ ENNReal.ofReal (3 / 2) := by
  have := eLpNorm_comb2_le (p := 2) (by norm_num) volume (g 3) (g 4) (aesm_g 3 _) (aesm_g 4 _) 1 (-1 / 2) 1 1
    (eLpNorm_g_two_le' (by norm_num : 1 ≤ 3)) (eLpNorm_g_two_le' (by norm_num : 1 ≤ 4))
    (by norm_num) (by norm_num)
  refine this.trans (le_of_eq ?_)
  congr 1; norm_num [abs_of_neg]

theorem eLpNorm_wg : eLpNorm wg 2 volume ≤ ENNReal.ofReal (5 / 2) := by
  have := eLpNorm_comb2_le (p := 2) (by norm_num) volume (g 3) (g 4) (aesm_g 3 _) (aesm_g 4 _) 1 (-3 / 2) 1 1
    (eLpNorm_g_two_le' (by norm_num : 1 ≤ 3)) (eLpNorm_g_two_le' (by norm_num : 1 ≤ 4))
    (by norm_num) (by norm_num)
  refine this.trans (le_of_eq ?_)
  congr 1; norm_num [abs_of_neg]

theorem eLpNorm_Gk : eLpNorm Gk 1 volume ≤ ENNReal.ofReal 3 := by
  have h12 := eLpNorm_comb2_le (p := 1) (by norm_num) volume (g 2) (g 3) (aesm_g 2 _) (aesm_g 3 _)
    1 (-3 / 2) 1 1 (eLpNorm_g_one_le (by norm_num)) (eLpNorm_g_one_le (by norm_num))
    (by norm_num) (by norm_num)
  have := eLpNorm_comb2_le (p := 1) (by norm_num) volume (fun t => 1 * g 2 t + (-3 / 2) * g 3 t) (g 4)
    (((aesm_g 2 _).const_mul 1).add ((aesm_g 3 _).const_mul (-3 / 2))) (aesm_g 4 _) 1 (1 / 2) _ 1 h12
    (eLpNorm_g_one_le (by norm_num)) (by positivity) (by norm_num)
  refine this.trans (le_of_eq ?_)
  congr 1; norm_num [abs_of_neg]

theorem eLpNorm_u2g : eLpNorm u2g 1 volume ≤ ENNReal.ofReal (15 / 2) := by
  have h12 := eLpNorm_comb2_le (p := 1) (by norm_num) volume (g 1) (g 2) (aesm_g 1 _) (aesm_g 2 _)
    1 (-3) 1 1 (eLpNorm_g_one_le (by norm_num)) (eLpNorm_g_one_le (by norm_num))
    (by norm_num) (by norm_num)
  have h123 := eLpNorm_comb2_le (p := 1) (by norm_num) volume (fun t => 1 * g 1 t + (-3) * g 2 t) (g 3)
    (((aesm_g 1 _).const_mul 1).add ((aesm_g 2 _).const_mul (-3))) (aesm_g 3 _) 1 (11 / 4) _ 1 h12
    (eLpNorm_g_one_le (by norm_num)) (by positivity) (by norm_num)
  have := eLpNorm_comb2_le (p := 1) (by norm_num) volume
    (fun t => 1 * (1 * g 1 t + (-3) * g 2 t) + (11 / 4) * g 3 t) (g 4)
    ((((aesm_g 1 _).const_mul 1).add ((aesm_g 2 _).const_mul (-3))).const_mul 1 |>.add
      ((aesm_g 3 _).const_mul (11 / 4)))
    (aesm_g 4 _) 1 (-3 / 4) _ 1 h123 (eLpNorm_g_one_le (by norm_num)) (by positivity) (by norm_num)
  refine this.trans (le_of_eq ?_)
  congr 1; norm_num [abs_of_neg]


theorem measurable_rconv (k f : ℝ → ℝ) (hk : Measurable k) (hf : Measurable f) :
    Measurable (GppCausalTail.rconv k f) := by
  have hG : Measurable (fun p : ℝ × ℝ => k p.2 * f (p.1 - p.2)) :=
    (hk.comp measurable_snd).mul (hf.comp (measurable_fst.sub measurable_snd))
  have := (hG.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have e : GppCausalTail.rconv k f = fun t => ∫ s, k s * f (t - s) := by
    funext t; exact GppCausalTail.rconv_apply k f t
  rw [e]; exact this

theorem measurable_u1g : Measurable u1g := by
  unfold u1g; have := measurable_g; fun_prop

theorem measurable_u2g : Measurable u2g := by
  unfold u2g; have := measurable_g; fun_prop

theorem u1g_neg {x : ℝ} (hx : x < 0) : u1g x = 0 := by simp [u1g, g_of_neg hx]
theorem u2g_neg {x : ℝ} (hx : x < 0) : u2g x = 0 := by simp [u2g, g_of_neg hx]

theorem u1g_eq {x : ℝ} (hx : 0 ≤ x) : u1g x = u1 x := by
  simp only [u1g, u1, g2_of_nonneg hx, g3_of_nonneg hx, g4_of_nonneg hx]; ring

theorem u2g_eq {x : ℝ} (hx : 0 ≤ x) : u2g x = u2 x := by
  have g1 : g 1 x = Real.exp (-x) := by simp [g, hx]
  simp only [u2g, u2, g1, g2_of_nonneg hx, g3_of_nonneg hx, g4_of_nonneg hx]; ring


/-- From an `L²` bound to the real integral bound. -/
theorem sq_of_eLpNorm (μ : Measure ℝ) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : 0 ≤ C) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    Integrable (fun t => f t ^ 2) μ ∧ ∫ t, f t ^ 2 ∂μ ≤ C ^ 2 := by
  have hmem : MemLp f 2 μ := ⟨hf, h.trans_lt ENNReal.ofReal_lt_top⟩
  have hint := hmem.integrable_sq
  refine ⟨hint, ?_⟩
  have h1 : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂μ = (eLpNorm f 2 μ) ^ 2 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    have e2 : ENNReal.toReal 2 = ((2:ℕ) : ℝ) := by simp
    simp only [e2, ENNReal.rpow_natCast]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have h2 : ENNReal.ofReal (∫ t, f t ^ 2 ∂μ) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t => sq_nonneg _)]
    refine lintegral_congr fun t => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  have h3 : ENNReal.ofReal (∫ t, f t ^ 2 ∂μ) ≤ ENNReal.ofReal (C ^ 2) := by
    rw [h2, h1, ENNReal.ofReal_pow hC]
    gcongr
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- From an `L¹` bound to the real integral bound. -/
theorem L1_of_eLpNorm (μ : Measure ℝ) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (hC : 0 ≤ C) (h : eLpNorm f 1 μ ≤ ENNReal.ofReal C) :
    Integrable f μ ∧ ∫ t, |f t| ∂μ ≤ C := by
  have hint : Integrable f μ := memLp_one_iff_integrable.1 ⟨hf, h.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨hint, ?_⟩
  have h2 := ofReal_integral_norm_eq_lintegral_enorm hint
  rw [← eLpNorm_one_eq_lintegral_enorm] at h2
  have h3 : ENNReal.ofReal (∫ t, ‖f t‖ ∂μ) ≤ ENNReal.ofReal C := h2.le.trans h
  have := (ENNReal.ofReal_le_ofReal_iff hC).1 h3
  simpa [Real.norm_eq_abs] using this


/-- The measure `μ₊ = volume` restricted to `(0, ∞)`. -/
noncomputable abbrev mu0 : Measure ℝ := volume.restrict (Ioi (0:ℝ))

theorem Z_ae : ∀ᵐ t ∂mu0, Z t = 1 * Gz t + (-1) * GppCausalTail.rconv ff0 u1g t := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [Z_formula ht0, rconv_ff0_eq (fun x hx => u1g_neg hx) t]
  have : ∫ u in Ioc (0:ℝ) t, ff u * u1 (t - u) = ∫ u in Ioc (0:ℝ) t, ff u * u1g (t - u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [u1g_eq (by linarith [hu.2])]
  rw [this]
  simp only [Gz]; ring

theorem kk_ae : ∀ᵐ t ∂mu0, kk t = 1 * Gk t + (-1) * GppCausalTail.rconv ff0 u2g t := by
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  have ht0 : 0 ≤ t := le_of_lt ht
  rw [kk_formula ht0, rconv_ff0_eq (fun x hx => u2g_neg hx) t]
  have : ∫ u in Ioc (0:ℝ) t, ff u * u2 (t - u) = ∫ u in Ioc (0:ℝ) t, ff u * u2g (t - u) :=
    setIntegral_congr_fun measurableSet_Ioc fun u hu => by rw [u2g_eq (by linarith [hu.2])]
  rw [this]
  simp only [Gk]; ring

theorem measurable_Gz : Measurable Gz := by unfold Gz; have := measurable_g; fun_prop
theorem measurable_Gk : Measurable Gk := by unfold Gk; have := measurable_g; fun_prop
theorem measurable_wg : Measurable wg := by unfold wg; have := measurable_g; fun_prop

theorem eLpNorm_Z_le : eLpNorm Z 2 mu0 ≤ ENNReal.ofReal 9 := by
  have hF : eLpNorm (GppCausalTail.rconv ff0 u1g) 2 volume ≤ ENNReal.ofReal (15 / 2) := by
    refine (eLpNorm_rconv_two_le ff0 u1g measurable_ff0 measurable_u1g).trans ?_
    calc eLpNorm ff0 1 volume * eLpNorm u1g 2 volume
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (15 / 4) := by
          gcongr
          · exact eLpNorm_ff0_le
          · exact eLpNorm_u1g
      _ = ENNReal.ofReal (15 / 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  have h1 : eLpNorm Gz 2 mu0 ≤ ENNReal.ofReal (3 / 2) :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans eLpNorm_Gz
  have h2 : eLpNorm (GppCausalTail.rconv ff0 u1g) 2 mu0 ≤ ENNReal.ofReal (15 / 2) :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hF
  have hm1 : AEStronglyMeasurable Gz mu0 := measurable_Gz.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (GppCausalTail.rconv ff0 u1g) mu0 :=
    (measurable_rconv ff0 u1g measurable_ff0 measurable_u1g).aestronglyMeasurable
  rw [eLpNorm_congr_ae Z_ae]
  refine (eLpNorm_comb2_le (by norm_num) mu0 Gz _ hm1 hm2 1 (-1) _ _ h1 h2 (by norm_num) (by norm_num)).trans ?_
  refine le_of_eq ?_
  congr 1; norm_num

theorem eLpNorm_kk_le : eLpNorm kk 1 mu0 ≤ ENNReal.ofReal 18 := by
  have hF : eLpNorm (GppCausalTail.rconv ff0 u2g) 1 volume ≤ ENNReal.ofReal 15 := by
    refine (eLpNorm_rconv_one_le ff0 u2g measurable_ff0 measurable_u2g).trans ?_
    calc eLpNorm ff0 1 volume * eLpNorm u2g 1 volume
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (15 / 2) := by
          gcongr
          · exact eLpNorm_ff0_le
          · exact eLpNorm_u2g
      _ = ENNReal.ofReal 15 := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
  have h1 : eLpNorm Gk 1 mu0 ≤ ENNReal.ofReal 3 :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans eLpNorm_Gk
  have h2 : eLpNorm (GppCausalTail.rconv ff0 u2g) 1 mu0 ≤ ENNReal.ofReal 15 :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans hF
  have hm1 : AEStronglyMeasurable Gk mu0 := measurable_Gk.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (GppCausalTail.rconv ff0 u2g) mu0 :=
    (measurable_rconv ff0 u2g measurable_ff0 measurable_u2g).aestronglyMeasurable
  rw [eLpNorm_congr_ae kk_ae]
  refine (eLpNorm_comb2_le (p := 1) (by norm_num) mu0 Gk _ hm1 hm2 1 (-1) _ _ h1 h2 (by norm_num) (by norm_num)).trans ?_
  refine le_of_eq ?_
  congr 1; norm_num

theorem eLpNorm_w_le : eLpNorm w 2 mu0 ≤ ENNReal.ofReal (5 / 2) := by
  have : w = wg := funext fun t => (wg_eq t).symm
  rw [this]
  exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans eLpNorm_wg


theorem measurable_nuConv (F : ℝ → ℝ) (hF : Measurable F) : Measurable (nuConv F) := by
  have h : Measurable (fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, F (p.1 - Real.log n) / Real.sqrt n) := by
    refine measurable_from_prod_countable_left fun N => ?_
    show Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, F (x - Real.log n) / Real.sqrt n
    exact Finset.measurable_sum (Finset.Icc 1 N) fun n _ =>
      (hF.comp (measurable_id.sub_const (Real.log n))).div_const (Real.sqrt n)
  have := h.comp (measurable_id.prodMk (Measurable.nat_floor Real.measurable_exp))
  exact this

theorem measurable_w : Measurable w := by
  have : w = wg := funext fun t => (wg_eq t).symm
  rw [this]; exact measurable_wg

theorem measurable_wd : Measurable wd := by
  have : wd = fun t => 1 * g 2 t + (-5 / 2) * g 3 t + (3 / 2) * g 4 t := by
    funext t; simp only [wd]; ring
  rw [this]; have := measurable_g; fun_prop

theorem measurable_Z : Measurable Z := measurable_nuConv w measurable_w
theorem measurable_kk : Measurable kk := measurable_nuConv wd measurable_wd
theorem measurable_hh (c : ℝ) : Measurable (hh c) := by
  unfold hh; exact measurable_w.sub (measurable_Z.const_mul c)

/-- `‖w‖_{L²(0,∞)} ≤ 5/2`, in the real-integral form used by Part A. -/
theorem w_sq_bound : IntegrableOn (fun t => w t ^ 2) (Ioi (0:ℝ)) ∧
    ∫ t in Ioi (0:ℝ), w t ^ 2 ≤ (5 / 2) ^ 2 :=
  sq_of_eLpNorm mu0 w measurable_w.aestronglyMeasurable (by norm_num) eLpNorm_w_le

/-- `‖Z‖_{L²(0,∞)} ≤ 9`. -/
theorem Z_sq_bound : IntegrableOn (fun t => Z t ^ 2) (Ioi (0:ℝ)) ∧
    ∫ t in Ioi (0:ℝ), Z t ^ 2 ≤ 9 ^ 2 :=
  sq_of_eLpNorm mu0 Z measurable_Z.aestronglyMeasurable (by norm_num) eLpNorm_Z_le

/-- `‖k‖_{L¹(0,∞)} ≤ 18`. -/
theorem kk_L1_bound : IntegrableOn kk (Ioi (0:ℝ)) ∧ ∫ s in Ioi (0:ℝ), |kk s| ≤ 18 :=
  L1_of_eLpNorm mu0 kk measurable_kk.aestronglyMeasurable (by norm_num) eLpNorm_kk_le

/-- `‖h‖_{L²(0,∞)} ≤ 5/2 + 9|c|` for `h = w − cZ`. -/
theorem hh_sq_bound (c : ℝ) : IntegrableOn (fun t => hh c t ^ 2) (Ioi (0:ℝ)) ∧
    ∫ t in Ioi (0:ℝ), hh c t ^ 2 ≤ (5 / 2 + 9 * |c|) ^ 2 := by
  have h := eLpNorm_comb2_le (p := 2) (by norm_num) mu0 w Z measurable_w.aestronglyMeasurable
    measurable_Z.aestronglyMeasurable 1 (-c) (5 / 2) 9 eLpNorm_w_le eLpNorm_Z_le (by norm_num)
    (by norm_num)
  have e : (fun t => 1 * w t + (-c) * Z t) = hh c := by
    funext t; simp only [hh]; ring
  rw [e] at h
  have h' : eLpNorm (hh c) 2 mu0 ≤ ENNReal.ofReal (5 / 2 + 9 * |c|) := by
    refine h.trans (le_of_eq ?_)
    congr 1; rw [abs_one, abs_neg]; ring
  exact sq_of_eLpNorm mu0 (hh c) (measurable_hh c).aestronglyMeasurable (by positivity) h'


end GppCausalNorms
