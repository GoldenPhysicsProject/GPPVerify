/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Meromorphic.Divisor
import GppVerify.Upstream.ZeroCounting
import GppVerify.Upstream.DyadicSummability
import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import GppVerify.RiemannHypothesis.XiOrder
import GppVerify.RiemannHypothesis.LogDerivativeZeroFree

/-!
# Explicit formula, stage E3b (part 1): multiplicities of `ξ` and `ζ` agree in the strip

For `0 < Re ρ < 1` the orders of vanishing of `ξ` and `ζ` at `ρ` coincide, because
`ξ(s) = s(s-1)/2 · Γℝ(s) · ζ(s)` with `s(s-1)/2 · Γℝ(s)` analytic and nonvanishing there.
-/

open Complex

namespace GppXiZeroCounting

open GppLogDerivZeroFree

theorem xi_zero_ne : xi 0 ≠ 0 := by
  unfold xi
  simp

/-- Near a point `ρ` with `0 < Re ρ < 1`, `ξ(s) · Γℝ(s)⁻¹ = s(s-1)/2 · ζ(s)`. -/
theorem xi_mul_Gammaℝ_inv_eventuallyEq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (fun s => xi s * (Gammaℝ s)⁻¹) =ᶠ[nhds ρ] fun s => (s * (s - 1) / 2) * riemannZeta s := by
  have hre : ∀ᶠ s in nhds ρ, 0 < s.re :=
    (continuous_re.continuousAt.eventually (lt_mem_nhds h0))
  have hre1 : ∀ᶠ s in nhds ρ, s.re < 1 :=
    (continuous_re.continuousAt.eventually (gt_mem_nhds h1))
  filter_upwards [hre, hre1] with s hs hs1r
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hg : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : riemannZeta s = completedRiemannZeta s / Gammaℝ s := riemannZeta_def_of_ne_zero hs0
  have hL : completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
    have := completedRiemannZeta_eq s
    linear_combination this
  have hs1 : s ≠ 1 := fun h => by simp [h] at hs1r
  have h1s : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  rw [hz, hL]
  unfold xi
  field_simp
  ring

theorem analyticAt_riemannZeta {ρ : ℂ} (h : ρ ≠ 1) : AnalyticAt ℂ riemannZeta ρ := by
  have hopen : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hd : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds h)

/-- **Orders of vanishing of `ξ` and `ζ` agree at every point of the open strip.** -/
theorem analyticOrderAt_xi_eq {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    analyticOrderAt xi ρ = analyticOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hxi : AnalyticAt ℂ xi ρ := differentiable_xi.analyticAt ρ
  have hinv : AnalyticAt ℂ (fun s => (Gammaℝ s)⁻¹) ρ :=
    differentiable_Gammaℝ_inv.analyticAt ρ
  have hinv0 : analyticOrderAt (fun s => (Gammaℝ s)⁻¹) ρ = 0 := by
    rw [hinv.analyticOrderAt_eq_zero]
    exact inv_ne_zero (Gammaℝ_ne_zero_of_re_pos h0)
  have hp : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) ρ := by fun_prop
  have hp0 : analyticOrderAt (fun s : ℂ => s * (s - 1) / 2) ρ = 0 := by
    rw [hp.analyticOrderAt_eq_zero]
    have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
    have : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
    exact div_ne_zero (mul_ne_zero hρ0 this) two_ne_zero
  have hz := analyticAt_riemannZeta hρ1
  have e1 : analyticOrderAt (fun s => xi s * (Gammaℝ s)⁻¹) ρ = analyticOrderAt xi ρ := by
    have := analyticOrderAt_mul hxi hinv
    rw [hinv0, add_zero] at this
    exact this
  have e2 : analyticOrderAt (fun s => (s * (s - 1) / 2) * riemannZeta s) ρ
      = analyticOrderAt riemannZeta ρ := by
    have := analyticOrderAt_mul hp hz
    rw [hp0, zero_add] at this
    exact this
  rw [← e1, ← e2]
  exact analyticOrderAt_congr (xi_mul_Gammaℝ_inv_eventuallyEq h0 h1)

theorem analyticOrderAt_xi_ne_top (ρ : ℂ) : analyticOrderAt xi ρ ≠ ⊤ := by
  intro htop
  have hev : xi =ᶠ[nhds ρ] 0 := analyticOrderAt_eq_top.1 htop
  have hon : AnalyticOnNhd ℂ xi Set.univ := fun z _ => differentiable_xi.analyticAt z
  have hzero := hon.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ ρ) hev
  have h0 : xi 0 = 0 := hzero (Set.mem_univ 0)
  exact xi_zero_ne h0

/-- The divisor of `ξ` on a closed ball is its (natural-number) order of vanishing. -/
theorem divisor_xi_apply {r : ℝ} {ρ : ℂ} (hρ : ρ ∈ Metric.closedBall (0 : ℂ) r) :
    MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r) ρ = (analyticOrderNatAt xi ρ : ℤ) := by
  have hon : AnalyticOnNhd ℂ xi (Metric.closedBall (0 : ℂ) r) :=
    fun z _ => differentiable_xi.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hon hρ]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top ρ)
  simp [analyticOrderNatAt, ← hn]

/-- Multiplicity of a zero of `ζ`: the order of vanishing. -/
noncomputable def zeroMult (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

/-- Nontrivial zeros of `ζ` have `ξ`-order equal to `ζ`-multiplicity. -/
theorem zeroMult_eq_orderNat_xi {ρ : ℂ} (hρ : ρ ∈ GppWeilCriterion.nontrivialZeros) :
    zeroMult ρ = analyticOrderNatAt xi ρ := by
  obtain ⟨-, h0, h1⟩ := hρ
  unfold zeroMult analyticOrderNatAt
  rw [analyticOrderAt_xi_eq h0 h1]

/-- **Polynomial zero counting, finite form.** There are constants `A`, `B` such that any finite
set of nontrivial zeros inside the closed ball of radius `r` has total multiplicity at most
`A + B r ^ 3`. (`ξ` has order `≤ 2`, and Jensen gives exponent `2 + 1`.) -/
theorem sum_zeroMult_le :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ), 0 < r → ∀ T : Finset ℂ,
      (∀ ρ ∈ T, ρ ∈ GppWeilCriterion.nontrivialZeros ∧ ‖ρ‖ ≤ r) →
      ((∑ ρ ∈ T, zeroMult ρ : ℕ) : ℝ) ≤ A + B * r ^ ((2 : ℝ) + 1) := by
  obtain ⟨A, B, hB, hb⟩ := Complex.HasOrderLE.sum_divisor_le differentiable_xi
    (by simpa using xi_zero_ne) GppXiOrder.xi_hasOrderLE_two (ε := 1) one_pos
  refine ⟨A, B, hB, fun r hr T hT => ?_⟩
  have hon : AnalyticOnNhd ℂ xi (Metric.closedBall (0 : ℂ) r) :=
    fun z _ => differentiable_xi.analyticAt z
  have hnn := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hon
  have hfin := (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  refine le_trans ?_ (hb r hr)
  have hmem : ∀ ρ ∈ T, ρ ∈ Metric.closedBall (0 : ℂ) r := fun ρ h => by
    simpa using (hT ρ h).2
  have hsum : ∑ ρ ∈ T, (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)) ρ
      = ((∑ ρ ∈ T, zeroMult ρ : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun ρ h => ?_
    rw [divisor_xi_apply (hmem ρ h), zeroMult_eq_orderNat_xi (hT ρ h).1]
  have hle : ∑ ρ ∈ T, (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)) ρ
      ≤ ∑ᶠ u, (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)) u := by
    rw [finsum_eq_sum_of_support_subset _
      (s := hfin.toFinset ∪ T) (by intro u hu; exact Finset.mem_union_left _ (hfin.mem_toFinset.2 hu))]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
      (fun u _ _ => hnn u)
  have : (((∑ ρ ∈ T, zeroMult ρ : ℕ) : ℤ) : ℝ) ≤
      ((∑ᶠ u, (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)) u : ℤ) : ℝ) := by
    exact_mod_cast hsum ▸ hle
  simpa using this

/-- Nontrivial zeros have multiplicity at least one. -/
theorem one_le_zeroMult {ρ : ℂ} (hρ : ρ ∈ GppWeilCriterion.nontrivialZeros) : 1 ≤ zeroMult ρ := by
  have hρ' := hρ
  obtain ⟨hz, h0, h1⟩ := hρ'
  rw [zeroMult_eq_orderNat_xi hρ]
  have hρ0 : ρ ≠ 0 := fun h => by simp [h] at h0
  have hρ1 : ρ ≠ 1 := fun h => by simp [h] at h1
  have hxi0 : xi ρ = 0 :=
    xi_eq_zero_of_zeta_zero hz hρ0 hρ1 (Gammaℝ_ne_zero_of_re_pos h0)
  have hne0 : analyticOrderAt xi ρ ≠ 0 := by
    rw [Ne, (differentiable_xi.analyticAt ρ).analyticOrderAt_eq_zero]
    simpa using hxi0
  have htop := analyticOrderAt_xi_ne_top ρ
  unfold analyticOrderNatAt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 htop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := fun h => hne0 (by simp [h])
  omega

/-- **E3b: polynomial zero counting.** Counting the nontrivial zeros of `ζ` with multiplicity,
`∑ mult(ρ) (1 + ‖ρ‖)⁻⁴` converges. -/
theorem zeroCountingPolynomial :
    ∃ N : ℕ, Summable (fun ρ : GppWeilCriterion.nontrivialZeros =>
      (zeroMult ρ : ℝ) * ((1 + ‖(ρ : ℂ)‖) ^ N)⁻¹) := by
  obtain ⟨A, B, hB, hcount⟩ := sum_zeroMult_le
  refine ⟨4, ?_⟩
  let ι := Σ ρ : GppWeilCriterion.nontrivialZeros, Fin (zeroMult ρ)
  let a : ι → ℝ := fun i => 1 + ‖(i.1 : ℂ)‖
  have hpos : ∀ i, 0 < a i := fun i => by simp only [a]; positivity
  -- finiteness of the zeros in a ball
  have hZfin : ∀ r : ℝ, {ρ : GppWeilCriterion.nontrivialZeros | ‖(ρ : ℂ)‖ ≤ r}.Finite := by
    intro r
    by_cases hr : 0 < r
    · have hon : AnalyticOnNhd ℂ xi (Metric.closedBall (0 : ℂ) r) :=
        fun z _ => differentiable_xi.analyticAt z
      have hfin := (MeromorphicOn.divisor xi (Metric.closedBall (0 : ℂ) r)).finiteSupport
        (isCompact_closedBall 0 r)
      refine Set.Finite.of_finite_image (f := Subtype.val) ?_ Subtype.val_injective.injOn
      refine hfin.subset ?_
      rintro _ ⟨ρ, hρ, rfl⟩
      have hmem : (ρ : ℂ) ∈ Metric.closedBall (0 : ℂ) r := by simpa using hρ
      rw [Function.mem_support, divisor_xi_apply hmem, ← zeroMult_eq_orderNat_xi ρ.2]
      have := one_le_zeroMult ρ.2
      omega
    · refine (Set.finite_empty).subset ?_
      intro ρ hρ
      exfalso
      have : ‖(ρ : ℂ)‖ ≤ r := hρ
      have hρ0 : (ρ : ℂ) ≠ 0 := fun h => by
        have := ρ.2.2.1; simp [h] at this
      have := norm_pos_iff.2 hρ0
      exact hr (lt_of_lt_of_le this ‹_›)
  have hfin : ∀ r : ℝ, {i : ι | a i ≤ r}.Finite := by
    intro r
    refine ((hZfin (r - 1)).biUnion (fun ρ _ => Set.finite_range (Sigma.mk ρ))).subset ?_
    intro i hi
    have : ‖(i.1 : ℂ)‖ ≤ r - 1 := by have : a i ≤ r := hi; simp only [a] at this; linarith
    exact Set.mem_biUnion (x := i.1) this ⟨i.2, rfl⟩
  have hcard : ∀ r : ℝ, 0 < r →
      (((hfin r).toFinset.card : ℕ) : ℝ) ≤ A + B * r ^ ((2 : ℝ) + 1) := by
    intro r hr
    set Tf := (hZfin (r - 1)).toFinset with hTf
    have hsub : (hfin r).toFinset ⊆ Tf.sigma (fun ρ => (Finset.univ : Finset (Fin (zeroMult ρ)))) := by
      intro i hi
      have hi' : a i ≤ r := (hfin r).mem_toFinset.1 hi
      have : ‖(i.1 : ℂ)‖ ≤ r - 1 := by simp only [a] at hi'; linarith
      exact Finset.mem_sigma.2 ⟨(hZfin (r - 1)).mem_toFinset.2 this, Finset.mem_univ _⟩
    have hc1 := Finset.card_le_card hsub
    rw [Finset.card_sigma] at hc1
    simp only [Finset.card_univ, Fintype.card_fin] at hc1
    set T : Finset ℂ := Tf.image Subtype.val with hT
    have hsumT : ∑ ρ ∈ T, zeroMult ρ = ∑ ρ ∈ Tf, zeroMult (ρ : ℂ) :=
      Finset.sum_image (fun x _ y _ h => Subtype.val_injective h)
    have hbound := hcount r hr T (by
      intro ρ hρ
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hρ
      refine ⟨x.2, ?_⟩
      have := (hZfin (r - 1)).mem_toFinset.1 hx
      have : ‖(x : ℂ)‖ ≤ r - 1 := this
      linarith)
    refine le_trans ?_ hbound
    rw [hsumT]
    exact_mod_cast hc1
  have hsum := Real.summable_inv_pow_of_counting_le hpos hfin hB (by norm_num : (0:ℝ) ≤ 2 + 1)
    (m := 4) (by norm_num) hcard
  have hfib := hsum.sigma
  refine hfib.congr (fun ρ => ?_)
  simp only [a, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [inv_pow]

end GppXiZeroCounting
