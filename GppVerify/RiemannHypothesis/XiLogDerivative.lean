/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
import GppVerify.Upstream.LogDerivativeLandau
import GppVerify.Upstream.AvoidFiniteSet
import GppVerify.RiemannHypothesis.XiZeroCounting
import GppVerify.RiemannHypothesis.XiOrder

/-!
# Explicit formula, stage E4b: a polynomial bound for `ξ'/ξ` at good heights

For every `T ≥ 1` there is a height `t ∈ [T, T+1]` such that `ξ` has no zero on the horizontal
segment `{σ + i t : -1 ≤ σ ≤ 2}` and `‖ξ'/ξ‖` is at most a fixed power of `t` on it.
-/

open Complex Metric Set

namespace GppXiZeroCounting

open GppLogDerivZeroFree

/-- A zero of `ξ` has order at least one. -/
theorem one_le_orderNat_xi {u : ℂ} (h : xi u = 0) : 1 ≤ analyticOrderNatAt xi u := by
  have hne0 : analyticOrderAt xi u ≠ 0 := by
    rw [Ne, (differentiable_xi.analyticAt u).analyticOrderAt_eq_zero]
    simpa using h
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top u)
  unfold analyticOrderNatAt
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_natCast]
  have : n ≠ 0 := fun h => hne0 (by simp [h])
  omega

/-- A point of `closedBall 0 r` is in the support of the divisor of `ξ` iff it is a zero. -/
theorem mem_support_divisor_xi_iff {r : ℝ} {u : ℂ} (hu : u ∈ closedBall (0 : ℂ) r) :
    u ∈ Function.support (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)) ↔ xi u = 0 := by
  rw [Function.mem_support, divisor_xi_apply hu]
  constructor
  · intro h
    by_contra hx
    apply h
    have : analyticOrderAt xi u = 0 := (differentiable_xi.analyticAt u).analyticOrderAt_eq_zero.2 hx
    simp [analyticOrderNatAt, this]
  · intro h
    have := one_le_orderNat_xi h
    omega

/-- The zeros of `ξ` in a closed ball form a finite set. -/
theorem finite_zeros_xi (r : ℝ) : {u : ℂ | ‖u‖ ≤ r ∧ xi u = 0}.Finite := by
  have hon : AnalyticOnNhd ℂ xi (closedBall (0 : ℂ) r) := fun z _ => differentiable_xi.analyticAt z
  have hfin := (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  refine hfin.subset ?_
  rintro u ⟨hu, hx⟩
  have hu' : u ∈ closedBall (0 : ℂ) r := by simpa using hu
  exact (mem_support_divisor_xi_iff hu').2 hx

/-- **A radius in `[R₀, R₀ + 1]` such that `ξ` has no zero on the circle.** -/
theorem exists_radius_no_zero (R₀ : ℝ) :
    ∃ R ∈ Icc R₀ (R₀ + 1), ∀ z : ℂ, ‖z‖ = R → xi z ≠ 0 := by
  have hfin : (norm '' {u : ℂ | ‖u‖ ≤ R₀ + 1 ∧ xi u = 0}).Finite := (finite_zeros_xi _).image _
  have hinf : (Icc R₀ (R₀ + 1)).Infinite := Icc_infinite (by linarith)
  obtain ⟨R, hR, hnot⟩ := hinf.exists_notMem_finset hfin.toFinset
  refine ⟨R, hR, fun z hz hx => hnot ?_⟩
  rw [Set.Finite.mem_toFinset]
  exact ⟨z, ⟨by rw [hz]; exact hR.2, hx⟩, hz⟩

/-- The divisor of `ξ` on any set is its order of vanishing, on that set. -/
theorem divisor_xi_apply_set {U : Set ℂ} {ρ : ℂ} (hρ : ρ ∈ U) :
    MeromorphicOn.divisor xi U ρ = (analyticOrderNatAt xi ρ : ℤ) := by
  have hon : AnalyticOnNhd ℂ xi U := fun z _ => differentiable_xi.analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hon hρ]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (analyticOrderAt_xi_ne_top ρ)
  simp [analyticOrderNatAt, ← hn]

/-- **Jensen counting in terms of the orders of vanishing.** -/
theorem sum_orderNat_le :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ r : ℝ, 0 < r →
      ((∑ u ∈ (finite_zeros_xi r).toFinset, analyticOrderNatAt xi u : ℕ) : ℝ)
        ≤ A + B * r ^ ((2 : ℝ) + 1) := by
  obtain ⟨A, B, hB, hb⟩ := Complex.HasOrderLE.sum_divisor_le differentiable_xi
    (by simpa using xi_zero_ne) GppXiOrder.xi_hasOrderLE_two (ε := 1) one_pos
  refine ⟨A, B, hB, fun r hr => le_trans (le_of_eq ?_) (hb r hr)⟩
  have hfin := (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)).finiteSupport
    (isCompact_closedBall 0 r)
  have hsub : Function.support (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)) ⊆
      ↑(finite_zeros_xi r).toFinset := by
    intro u hu
    have hu' : u ∈ closedBall (0 : ℂ) r :=
      (MeromorphicOn.divisor xi (closedBall (0 : ℂ) r)).supportWithinDomain hu
    have := (mem_support_divisor_xi_iff hu').1 hu
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact ⟨by simpa using hu', this⟩
  have hfs : ∑ᶠ u, MeromorphicOn.divisor xi (closedBall (0 : ℂ) r) u =
      ∑ u ∈ (finite_zeros_xi r).toFinset, MeromorphicOn.divisor xi (closedBall (0 : ℂ) r) u :=
    finsum_eq_sum_of_support_subset _ hsub
  rw [hfs]
  have : ∑ u ∈ (finite_zeros_xi r).toFinset, MeromorphicOn.divisor xi (closedBall (0 : ℂ) r) u =
      ((∑ u ∈ (finite_zeros_xi r).toFinset, analyticOrderNatAt xi u : ℕ) : ℤ) := by
    push_cast
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [Set.Finite.mem_toFinset] at hu
    have hu' : u ∈ closedBall (0 : ℂ) r := by simpa using hu.1
    exact divisor_xi_apply_set hu'
  rw [this]
  push_cast
  rfl

/-- **E4b: a polynomial bound for `ξ'/ξ` on a horizontal segment at a good height.**
There are `K` and `C > 0` such that for every `T ≥ 1` some `t ∈ [T, T+1]` has `ξ ≠ 0` on the
segment `{σ + i t : -1 ≤ σ ≤ 2}` and `‖ξ'/ξ‖ ≤ C t^K` there. -/
theorem exists_good_height :
    ∃ (K : ℕ) (C : ℝ), 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∃ t ∈ Icc T (T + 1),
      ∀ σ ∈ Icc (-1 : ℝ) 2, xi ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 ∧
        ‖logDeriv xi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C * t ^ K := by
  obtain ⟨A, B, hB, hcount⟩ := sum_orderNat_le
  obtain ⟨C0, hC0, hgrow⟩ := GppXiOrder.xi_hasOrderLE_two 1 one_pos
  set a : ℝ := |A| + B + 1 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith [abs_nonneg A]
  set c1 : ℝ := |Real.log C0| + |Real.log ‖xi 0‖| + 2 with hc1
  refine ⟨6, (a * (2 * a + 6) + 48 * c1) * 11 ^ 6, by positivity, fun T hT => ?_⟩
  -- a radius with no zeros on the circle
  obtain ⟨R, hRI, hRz⟩ := exists_radius_no_zero (2 * T + 8)
  have hR10 : 10 ≤ R := by linarith [hRI.1]
  have hRpos : 0 < R := by linarith
  have hR11 : R ≤ 11 * T := by linarith [hRI.2]
  -- the zeros in the closed ball
  set S := (finite_zeros_xi R).toFinset with hS
  set n : ℕ := ∑ u ∈ S, analyticOrderNatAt xi u with hn
  have hR3 : R ^ ((2 : ℝ) + 1) = R ^ 3 := by
    rw [show ((2 : ℝ) + 1) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  set X : ℝ := A + B * R ^ 3 with hX
  have hnX : (n : ℝ) ≤ X := by
    have := hcount R hRpos
    rw [hR3] at this
    exact this
  have hX0 : 0 ≤ X := le_trans (Nat.cast_nonneg _) hnX
  have hXa : X ≤ a * R ^ 3 := by
    have hR31 : 1 ≤ R ^ 3 := one_le_pow₀ (by linarith)
    have : A ≤ |A| * R ^ 3 := by nlinarith [le_abs_self A, abs_nonneg A]
    rw [hX, ha]
    nlinarith
  set N : ℕ := ⌈X⌉₊ with hN
  have hNX : (N : ℝ) ≤ X + 1 := (Nat.ceil_lt_add_one hX0).le
  have hnN : n ≤ N := by
    have : (n : ℝ) ≤ N := hnX.trans (Nat.le_ceil X)
    exact_mod_cast this
  -- the ordinates of the zeros
  have hcard : S.card ≤ n := by
    rw [hn, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun u hu => ?_
    rw [hS, Set.Finite.mem_toFinset] at hu
    exact one_le_orderNat_xi hu.2
  set F : Finset ℝ := S.image (fun u => u.im) with hF
  have hFc : F.card ≤ N := (Finset.card_image_le.trans hcard).trans hnN
  obtain ⟨t, htI, htF⟩ := Real.exists_mem_Icc_far_from_finset T F hFc
  refine ⟨t, htI, fun σ hσ => ?_⟩
  have hδ : 0 < 1 / (2 * ((N : ℝ) + 1)) := by positivity
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsim : s.im = t := by simp [hs]
  have htT : T ≤ t := htI.1
  have htT1 : t ≤ T + 1 := htI.2
  have hsn : ‖s‖ ≤ R / 2 := by
    have h1 : ‖(σ : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]; constructor <;> linarith [hσ.1, hσ.2]
    have h2 : ‖(t : ℂ) * Complex.I‖ ≤ T + 1 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      exact htT1
    calc ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(t : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ R / 2 := by linarith [hRI.1]
  have hxs : xi s ≠ 0 := by
    intro h
    have hsS : s ∈ S := by
      rw [hS, Set.Finite.mem_toFinset]
      exact ⟨by linarith, h⟩
    have := htF s.im (Finset.mem_image_of_mem _ hsS)
    rw [hsim, sub_self, abs_zero] at this
    linarith
  refine ⟨hxs, ?_⟩
  have hM : ∀ z : ℂ, ‖z‖ ≤ R → ‖xi z‖ ≤ C0 * Real.exp (R ^ 3) := by
    intro z hz
    refine (hgrow z).trans ?_
    gcongr
    rw [← hR3]
    exact Real.rpow_le_rpow (norm_nonneg _) hz (by norm_num)
  have hL := Complex.norm_logDeriv_le differentiable_xi (by simpa using xi_zero_ne) hRpos hRz hM
    hsn hxs
  -- the sum over zeros
  have hδle : ∀ u ∈ S, 1 / (2 * ((N : ℝ) + 1)) ≤ ‖s - u‖ := by
    intro u hu
    have h1 := htF u.im (Finset.mem_image_of_mem _ hu)
    have h2 : |(s - u).im| ≤ ‖s - u‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hsim] at h2
    exact h1.trans h2
  have hDle : ∀ u : ℂ, (((MeromorphicOn.divisor xi (ball (0 : ℂ) R)) u).toNat : ℝ) ≤
      (analyticOrderNatAt xi u : ℝ) := by
    intro u
    by_cases hu : u ∈ ball (0 : ℂ) R
    · rw [divisor_xi_apply_set hu]; simp
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]; simp
  have hsupp : Function.support (fun u : ℂ =>
      (((MeromorphicOn.divisor xi (ball (0 : ℂ) R)) u).toNat : ℝ) * (1 / ‖s - u‖ + 2 / R)) ⊆ ↑S := by
    intro u hu
    rw [Function.mem_support] at hu
    have hD : (MeromorphicOn.divisor xi (ball (0 : ℂ) R)) u ≠ 0 := by
      intro h0'
      apply hu
      simp [h0']
    have hub : u ∈ ball (0 : ℂ) R :=
      (MeromorphicOn.divisor xi (ball (0 : ℂ) R)).supportWithinDomain (Function.mem_support.2 hD)
    rw [divisor_xi_apply_set hub] at hD
    have hord : analyticOrderNatAt xi u ≠ 0 := by exact_mod_cast hD
    have hxu : xi u = 0 := by
      by_contra hx
      apply hord
      have : analyticOrderAt xi u = 0 := (differentiable_xi.analyticAt u).analyticOrderAt_eq_zero.2 hx
      simp [analyticOrderNatAt, this]
    rw [Finset.mem_coe, hS, Set.Finite.mem_toFinset]
    exact ⟨by simpa using (ball_subset_closedBall hub), hxu⟩
  have hfac : ∀ u ∈ S, (1 / ‖s - u‖ + 2 / R) ≤ 2 * X + 6 := by
    intro u hu
    have h1 : 1 / ‖s - u‖ ≤ 2 * ((N : ℝ) + 1) := by
      have := one_div_le_one_div_of_le hδ (hδle u hu)
      rwa [one_div_one_div] at this
    have h2 : 2 / R ≤ 2 := by
      rw [div_le_iff₀ hRpos]; nlinarith
    linarith
  have hsum : ∑ᶠ u : ℂ, (((MeromorphicOn.divisor xi (ball (0 : ℂ) R)) u).toNat : ℝ) *
      (1 / ‖s - u‖ + 2 / R) ≤ X * (2 * X + 6) := by
    rw [finsum_eq_sum_of_support_subset _ hsupp]
    calc ∑ u ∈ S, (((MeromorphicOn.divisor xi (ball (0 : ℂ) R)) u).toNat : ℝ) *
          (1 / ‖s - u‖ + 2 / R)
        ≤ ∑ u ∈ S, (analyticOrderNatAt xi u : ℝ) * (2 * X + 6) := by
          refine Finset.sum_le_sum fun u hu => ?_
          have hnn : 0 ≤ 1 / ‖s - u‖ + 2 / R := by positivity
          exact mul_le_mul (hDle u) (hfac u hu) hnn (Nat.cast_nonneg _)
      _ = (n : ℝ) * (2 * X + 6) := by
          rw [← Finset.sum_mul, hn]; push_cast; rfl
      _ ≤ X * (2 * X + 6) := mul_le_mul_of_nonneg_right hnX (by linarith)
  -- the second term
  set P : ℝ := R ^ 3 with hP
  have hP1 : 1 ≤ P := one_le_pow₀ (by linarith)
  have hc1' : 2 ≤ c1 := by rw [hc1]; linarith [abs_nonneg (Real.log C0), abs_nonneg (Real.log ‖xi 0‖)]
  have hlogM : Real.log (C0 * Real.exp P) = Real.log C0 + P := by
    rw [Real.log_mul hC0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hsec : 24 * (Real.log (C0 * Real.exp P) - Real.log ‖xi 0‖ + 1) / R ≤ 48 * c1 * P := by
    rw [hlogM, div_le_iff₀ hRpos]
    have h1 : Real.log C0 ≤ |Real.log C0| := le_abs_self _
    have h2 : -Real.log ‖xi 0‖ ≤ |Real.log ‖xi 0‖| := neg_le_abs _
    have h3 : Real.log C0 + P - Real.log ‖xi 0‖ + 1 ≤ 2 * c1 * P := by
      rw [hc1] at hc1' ⊢
      nlinarith [abs_nonneg (Real.log C0), abs_nonneg (Real.log ‖xi 0‖)]
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ c1) (by linarith : (0 : ℝ) ≤ P))
      (by linarith : (0 : ℝ) ≤ R - 1)]
  have hXP : X ≤ a * P := hXa
  have hP2le : P ≤ P ^ 2 := by nlinarith
  have hX2 : X * (2 * X + 6) ≤ a * (2 * a + 6) * P ^ 2 := by
    have h1 : X * (2 * X + 6) ≤ (a * P) * (2 * (a * P) + 6) :=
      mul_le_mul hXP (by linarith) (by linarith) (by positivity)
    have h2 : 6 * a * P ≤ 6 * a * P ^ 2 :=
      mul_le_mul_of_nonneg_left hP2le (by linarith)
    calc X * (2 * X + 6) ≤ (a * P) * (2 * (a * P) + 6) := h1
      _ = 2 * a ^ 2 * P ^ 2 + 6 * a * P := by ring
      _ ≤ 2 * a ^ 2 * P ^ 2 + 6 * a * P ^ 2 := by linarith
      _ = a * (2 * a + 6) * P ^ 2 := by ring
  have hfinal : ‖logDeriv xi s‖ ≤ (a * (2 * a + 6) + 48 * c1) * P ^ 2 := by
    have h2 : 48 * c1 * P ≤ 48 * c1 * P ^ 2 :=
      mul_le_mul_of_nonneg_left hP2le (by linarith)
    have h3 : (a * (2 * a + 6) + 48 * c1) * P ^ 2 = a * (2 * a + 6) * P ^ 2 + 48 * c1 * P ^ 2 := by
      ring
    linarith [hL, hsum, hsec, hX2]
  have hP2 : P ^ 2 = R ^ 6 := by rw [hP]; ring
  have hRt : R ≤ 11 * t := by linarith
  have hR6 : R ^ 6 ≤ 11 ^ 6 * t ^ 6 := by
    calc R ^ 6 ≤ (11 * t) ^ 6 := pow_le_pow_left₀ hRpos.le hRt 6
      _ = 11 ^ 6 * t ^ 6 := by ring
  calc ‖logDeriv xi s‖ ≤ (a * (2 * a + 6) + 48 * c1) * P ^ 2 := hfinal
    _ ≤ (a * (2 * a + 6) + 48 * c1) * (11 ^ 6 * t ^ 6) := by
        rw [hP2]; gcongr
    _ = (a * (2 * a + 6) + 48 * c1) * 11 ^ 6 * t ^ 6 := by ring

end GppXiZeroCounting
