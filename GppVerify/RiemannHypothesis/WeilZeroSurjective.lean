/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.WeilZeroEmbedding
import GppVerify.RiemannHypothesis.ExponentialSumUnique
import GppVerify.RiemannHypothesis.XiZeroSymmetry

/-!
# Density of the states in the real form of `ℓ²(zeros)`

Assume `OnLine`. For a real test function `f`, `state f` lies in the real form
`{w : w_{ρ̄} = conj w_ρ}` of `ℓ²(zeros)` (`state_isRealForm`): zeros come in conjugate pairs with equal
multiplicity and `Ψ_f(ρ̄) = conj Ψ_f(ρ)`. Conversely, a vector `w` of the real form that is orthogonal
(real part of the inner product) to every `state f` is `0` (`eq_zero_of_orthogonal_states`).

Proof. Orthogonality to `state (f(· - t))` for all `t` says `Σ_ρ c_ρ e^{iγ_ρ t}` has real part `0`, where
`c_ρ = conj (w_ρ) √m_ρ Ψ_f(ρ)` is absolutely summable; the sum is real because the terms at `ρ` and
`ρ̄` are conjugate, hence it is `0`; the zeros have pairwise distinct ordinates `γ_ρ`, so
`GppExpSum.eq_zero_of_exponential_sum_eq_zero` gives `c_ρ = 0` for every `ρ`; a test function with
`Ψ_f(ρ) ≠ 0` then forces `w_ρ = 0`.
-/

open Complex MeasureTheory GppMeyerSpectralWeil GppWeilHilbert GppZeroHilbert GppWeilZero
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace GppWeilSurj

/-- The conjugate zero. -/
def conjZ (ρ : Zero) : Zero := ⟨starRingEnd ℂ ρ, GppXiZeroCounting.conj_mem_nontrivialZeros ρ.2⟩

@[simp] theorem coe_conjZ (ρ : Zero) : ((conjZ ρ : Zero) : ℂ) = starRingEnd ℂ (ρ : ℂ) := rfl

theorem conjZ_conjZ (ρ : Zero) : conjZ (conjZ ρ) = ρ := Subtype.ext (by simp)

/-- The real form of `ℓ²(zeros)`: `w_{ρ̄} = conj w_ρ`. -/
def IsRealForm (w : H) : Prop := ∀ ρ : Zero, w (conjZ ρ) = starRingEnd ℂ (w ρ)

theorem amp_conjZ (f : ℝ → ℝ) (ρ : Zero) : amp f (conjZ ρ) = starRingEnd ℂ (amp f ρ) := by
  have hm : GppXiZeroCounting.zeroMult ((conjZ ρ : Zero) : ℂ) = GppXiZeroCounting.zeroMult (ρ : ℂ) :=
    (GppXiZeroCounting.zeroData_symmetric ρ.2).2.2.2
  unfold amp
  rw [hm, map_mul, Complex.conj_ofReal]
  congr 1
  rw [coe_conjZ, ← GppBTSigmaSpectralTransform.spectralTransform_conj]

theorem state_isRealForm (hL : OnLine) (f : Test) : IsRealForm (state hL f) :=
  fun ρ => amp_conjZ f.1 ρ

theorem im_conjZ (ρ : Zero) : ((conjZ ρ : Zero) : ℂ).im = -(ρ : ℂ).im := by simp

theorem im_injective (hL : OnLine) : Function.Injective fun ρ : Zero => (ρ : ℂ).im := by
  intro a b hab
  refine Subtype.ext (Complex.ext ?_ hab)
  simp only at hab
  rw [hL a a.2, hL b b.2]

theorem phase_eq (hL : OnLine) (t : ℝ) (ρ : Zero) :
    phase t ρ = Complex.exp (((ρ : ℂ).im : ℂ) * t * Complex.I) := by
  unfold phase
  congr 1
  have : (ρ : ℂ) - 1 / 2 = (((ρ : ℂ).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hL ρ ρ.2]
  rw [this]; ring


/-- A test function whose transform at `1/2 + iγ` has positive real part. -/
theorem exists_test_re_pos (γ : ℝ) :
    ∃ f : ℝ → ℝ, IsTestFunction f ∧
      0 < (spectralTransform f (1 / 2 + (γ : ℂ) * Complex.I)).re := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun u => b u * Real.cos (γ * u), ⟨?_, ?_⟩, ?_⟩
  · exact b.contDiff.mul (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))
  · exact b.hasCompactSupport.mul_right
  · unfold spectralTransform
    have hcont : Continuous fun u : ℝ => b u * Real.cos (γ * u) :=
      b.continuous.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    have hsupp : HasCompactSupport fun u : ℝ => b u * Real.cos (γ * u) :=
      b.hasCompactSupport.mul_right
    have hint : Integrable fun u : ℝ =>
        ((b u * Real.cos (γ * u) : ℝ) : ℂ) * Complex.exp ((1 / 2 + (γ : ℂ) * Complex.I - 1 / 2) * u) := by
      refine (Continuous.mul (Complex.continuous_ofReal.comp hcont) (by fun_prop)).integrable_of_hasCompactSupport ?_
      exact (hsupp.comp_left Complex.ofReal_zero).mul_right
    have hr := (integral_re hint).symm
    simp only [RCLike.re_to_complex] at hr
    beta_reduce
    rw [hr]
    have hre : ∀ u : ℝ, (((b u * Real.cos (γ * u) : ℝ) : ℂ) *
        Complex.exp ((1 / 2 + (γ : ℂ) * Complex.I - 1 / 2) * u)).re = b u * Real.cos (γ * u) ^ 2 := by
      intro u
      have : (1 / 2 + (γ : ℂ) * Complex.I - 1 / 2) * (u : ℂ) = ((γ * u : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      ring
    simp_rw [hre]
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) ?_ ?_ ?_ ?_
    · exact b.continuous.mul ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2)
    · exact b.hasCompactSupport.mul_right
    · intro u; exact mul_nonneg b.nonneg (sq_nonneg _)
    · simp [b.one_of_mem_closedBall (x := (0 : ℝ)) (by simp [b])]

theorem exists_test_amp_ne (hL : OnLine) (ρ : Zero) : ∃ f : Test, amp f.1 ρ ≠ 0 := by
  obtain ⟨f, hf, hpos⟩ := exists_test_re_pos (ρ : ℂ).im
  have hρ : (ρ : ℂ) = 1 / 2 + (((ρ : ℂ).im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hL ρ ρ.2]
  refine ⟨⟨f, hf⟩, ?_⟩
  unfold amp
  have hm : (0 : ℝ) < Real.sqrt (GppXiZeroCounting.zeroMult (ρ : ℂ)) := by
    apply Real.sqrt_pos.2
    exact_mod_cast GppXiZeroCounting.one_le_zeroMult ρ.2
  refine mul_ne_zero (by exact_mod_cast hm.ne') ?_
  intro h0
  rw [hρ] at h0
  rw [h0] at hpos
  simp at hpos

theorem summable_c (hL : OnLine) (w : H) {f : ℝ → ℝ} (hf : IsTestFunction f) :
    Summable fun ρ : Zero => ‖starRingEnd ℂ (w ρ) * amp f ρ‖ := by
  have hw : Summable (fun ρ : Zero => ‖w ρ‖ ^ 2) := by
    have := (memℓp_gen_iff (p := (2 : ENNReal)) (by simp)).1 w.2
    simpa [Real.rpow_two] using this
  have ha : Summable (fun ρ : Zero => ‖amp f ρ‖ ^ 2) := by
    simp_rw [norm_amp_sq]; exact summable_sq hf hL
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ρ => ?_)
    ((hw.add ha).mul_left (1 / 2))
  rw [norm_mul, Complex.norm_conj]
  nlinarith [sq_nonneg (‖w ρ‖ - ‖amp f ρ‖)]


/-- The orbit coefficients of `w` against `state f`. -/
def coef (w : H) (f : ℝ → ℝ) (ρ : Zero) : ℂ := starRingEnd ℂ (w ρ) * amp f ρ

theorem coef_conjZ (w : H) (hw : IsRealForm w) (f : ℝ → ℝ) (ρ : Zero) :
    coef w f (conjZ ρ) = starRingEnd ℂ (coef w f ρ) := by
  unfold coef
  rw [hw ρ, amp_conjZ, map_mul, Complex.conj_conj]

/-- **Density of the states in the real form.** A vector of the real form of `ℓ²(zeros)` that is
orthogonal (in the real part of the inner product) to every `state f` is zero. -/
theorem eq_zero_of_orthogonal_states (hL : OnLine) (w : H) (hw : IsRealForm w)
    (h : ∀ f : Test, (inner ℂ w (state hL f)).re = 0) : w = 0 := by
  ext ρ0
  obtain ⟨f, hf⟩ := exists_test_amp_ne hL ρ0
  have hcs : Summable fun ρ => ‖coef w f.1 ρ‖ := summable_c hL w f.2
  -- the exponential sum vanishes for every `t`
  have hS : ∀ t : ℝ, ∑' ρ : Zero, coef w f.1 ρ *
      Complex.exp ((((ρ : ℂ).im : ℝ) : ℂ) * t * Complex.I) = 0 := by
    intro t
    have hinner : inner ℂ w (state hL ⟨shift t f.1, isTestFunction_shift t f.2⟩) =
        ∑' ρ : Zero, coef w f.1 ρ * Complex.exp ((((ρ : ℂ).im : ℝ) : ℂ) * t * Complex.I) := by
      rw [lp.inner_eq_tsum]
      refine tsum_congr fun ρ => ?_
      rw [RCLike.inner_apply]
      show amp (shift t f.1) ρ * starRingEnd ℂ (w ρ) = _
      have hs : amp (shift t f.1) ρ = phase t ρ * amp f.1 ρ := by
        unfold amp
        rw [spectralTransform_shift]
        unfold phase
        ring
      rw [hs, phase_eq hL]
      unfold coef
      ring
    have hre := h ⟨shift t f.1, isTestFunction_shift t f.2⟩
    rw [hinner] at hre
    set S := ∑' ρ : Zero, coef w f.1 ρ * Complex.exp ((((ρ : ℂ).im : ℝ) : ℂ) * t * Complex.I)
      with hSdef
    have hconj : starRingEnd ℂ S = S := by
      let e : Zero ≃ Zero := Function.Involutive.toPerm conjZ conjZ_conjZ
      have hterm : ∀ ρ : Zero, starRingEnd ℂ (coef w f.1 ρ *
          Complex.exp ((((ρ : ℂ).im : ℝ) : ℂ) * t * Complex.I)) =
          coef w f.1 (e ρ) * Complex.exp ((((e ρ : Zero) : ℂ).im : ℝ) * t * Complex.I) := by
        intro ρ
        show _ = coef w f.1 (conjZ ρ) * Complex.exp ((((conjZ ρ : Zero) : ℂ).im : ℝ) * t * Complex.I)
        rw [coef_conjZ w hw, im_conjZ, map_mul, ← Complex.exp_conj]
        congr 2
        simp [Complex.conj_ofReal]
      rw [hSdef, Complex.conj_tsum]
      simp_rw [hterm]
      exact e.tsum_eq (fun ρ => coef w f.1 ρ *
        Complex.exp ((((ρ : ℂ).im : ℝ) : ℂ) * t * Complex.I))
    have him : S.im = 0 := Complex.conj_eq_iff_im.1 hconj
    exact Complex.ext hre him
  have hc0 := GppExpSum.eq_zero_of_exponential_sum_eq_zero (fun ρ : Zero => (ρ : ℂ).im)
    (im_injective hL) (coef w f.1) hcs hS ρ0
  unfold coef at hc0
  have : starRingEnd ℂ (w ρ0) = 0 := (mul_eq_zero.1 hc0).resolve_right hf
  simpa using this

theorem continuous_coord (ρ : Zero) : Continuous fun v : H => v ρ := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun a b => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  have := lp.norm_apply_le_norm (by simp) (a - b) ρ
  simpa [lp.coeFn_sub] using this

section Packaged

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  {ι : testSubmodule →ₗ[ℝ] K}

/-- The image of the embedding lies in the real form. -/
theorem Jmap_isRealForm (hL : OnLine) (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (x : K) : IsRealForm (Jmap hL hι x) := by
  have hcl : IsClosed {x : K | IsRealForm (Jmap hL hι x)} := by
    have : {x : K | IsRealForm (Jmap hL hι x)} =
        ⋂ ρ : Zero, {x : K | Jmap hL hι x (conjZ ρ) = starRingEnd ℂ (Jmap hL hι x ρ)} := by
      ext x; simp [IsRealForm]
    rw [this]
    refine isClosed_iInter fun ρ => isClosed_eq ?_ ?_
    · exact (continuous_coord (conjZ ρ)).comp (Jmap hL hι).continuous
    · exact (Complex.continuous_conj.comp ((continuous_coord ρ).comp (Jmap hL hι).continuous))
  refine hd.induction_on x hcl (fun f => ?_)
  rw [Jmap_apply hL hι hd]
  exact state_isRealForm hL ⟨f.1, f.2⟩

/-- **Surjectivity of `J` onto the real form, as density.** A vector of the real form of
`ℓ²(zeros)` orthogonal to the whole image of the arithmetic Hilbert space is zero. Together with
`Jmap_isRealForm` (the image lies in the real form) and the isometry `Jmap_norm`, this identifies the
arithmetic space with the real form of `ℓ²` of the zeros. -/
theorem eq_zero_of_orthogonal_range (hL : OnLine)
    (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (hd : DenseRange ι)
    (w : H) (hw : IsRealForm w) (h : ∀ x : K, (inner ℂ w (Jmap hL hι x)).re = 0) : w = 0 :=
  eq_zero_of_orthogonal_states hL w hw fun f => by
    have := h (ι ⟨f.1, f.2⟩)
    rwa [Jmap_apply hL hι hd] at this

end Packaged

/-- **The arithmetic Hilbert space is the real form of `ℓ²(zeros)`** (under `h : RiemannHypothesis`):
the completion `K` of test functions under the Weil form, with its unitary dilation group, embeds by a
norm-preserving `J` into the real form of `ℓ²` of the nontrivial zeros, `J (ι f) = state f`,
equivariantly, and a vector of the real form orthogonal to the whole image is zero. -/
theorem arithmetic_space_is_real_form (h : RiemannHypothesis) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (ι : testSubmodule →ₗ[ℝ] K) (J : K →L[ℝ] H),
      (∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) ∧ DenseRange ι ∧
      (∀ x, ‖J x‖ = ‖x‖) ∧ (∀ f : testSubmodule, J (ι f) = state (GppInstantiated.onLine h)
        ⟨f.1, f.2⟩) ∧ (∀ x, IsRealForm (J x)) ∧
      (∀ w : H, IsRealForm w → (∀ x : K, (inner ℂ w (J x)).re = 0) → w = 0) := by
  obtain ⟨K, _, _, _, ι, hι, hd⟩ := exists_hilbert_weil (GppInstantiated.arp h)
  have hL := GppInstantiated.onLine h
  exact ⟨K, inferInstance, inferInstance, inferInstance, ι, Jmap hL hι, hι, hd,
    Jmap_norm hL hι hd, fun f => Jmap_apply hL hι hd f, Jmap_isRealForm hL hι hd,
    fun w hw hx => eq_zero_of_orthogonal_range hL hι hd w hw hx⟩

end GppWeilSurj

#print axioms GppWeilSurj.eq_zero_of_orthogonal_states
#print axioms GppWeilSurj.Jmap_isRealForm
#print axioms GppWeilSurj.arithmetic_space_is_real_form
