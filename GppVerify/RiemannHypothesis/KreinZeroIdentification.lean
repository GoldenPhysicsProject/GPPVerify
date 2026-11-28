/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.ZeroHilbertSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The Krein-type identification on `ℓ²(zeros)`, with no line hypothesis (T4)

`ZeroHilbertSpace` builds the state `f ↦ (√m_ρ Ψ_f(ρ))_ρ` and proves the norm identity
`‖state f‖² = weilForm (autocorr f)` **under `OnLine`**. This module removes that hypothesis from
the construction and keeps the identity in its honest unconditional form.

Everything below is stated and proved without `OnLine`:

* `amp f ∈ ℓ²(zeros)` for every test function `f` (`memℓp_amp_unconditional`): the squared
  coordinates are bounded by `sup |Ψ_f|` on the strip times the absolutely convergent zero sum.
* The reflection `T` of `ℓ²(zeros)` is the permutation `ρ ↦ 1 − ρ̄` (`zetaInvolution`), a
  unitary self-adjoint involution (`reflect`, `reflect_reflect`, `inner_reflect_left`).
* **Krein-type identity** (`weilForm_autocorr_eq_inner_reflect`):
  `weilForm (autocorr f) = ⟨T (S f), S f⟩`, where `S f = (√m_ρ Ψ_f(ρ))_ρ`. It is the explicit
  formula (`explicit_formula_zeroSum`) combined with the pairing form of `gwef2_factorisation`.
* `T` is the identity exactly when every zero is on the line (`reflect_eq_self_iff_onLine`), and a
  zero is fixed by `ρ ↦ 1 − ρ̄` exactly when `Re ρ = 1/2` (`zetaInvolution_fixed_iff`).
* **Coordinatewise exactness** (`coordinate_norm_eq_iff`): at a given zero `ρ`, the
  Krein term of `f` equals the norm term of `f` for every test function `f` exactly when
  `Re ρ = 1/2`. The proof separates the two evaluation points with test functions and uses no
  line hypothesis.
* Under `OnLine`, `S f` is the state of `ZeroHilbertSpace` and the identity is
  `inner_state_self` (`stateU_eq_state`, `krein_identity_online`).

Reading: this is a zero-indexed identification. Positivity of the Krein form is the Weil
criterion, which this file neither proves nor assumes; the unconditional content is that the
arithmetic form is a Krein-type pairing on `ℓ²(zeros)` whose fundamental symmetry is the
reflection in the critical line.
-/

open Complex MeasureTheory GppMeyerSpectralWeil GppXiZeroCounting GppWeilCriterion
  GppArithmeticReflection GppZeroHilbert
open scoped ComplexConjugate ENNReal

noncomputable section

namespace GppKreinZero

/-! ## The state, without `OnLine` -/

theorem summable_norm_term {f : ℝ → ℝ} (hf : IsTestFunction f) :
    Summable (fun ρ : Zero => (zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖) := by
  have h := (GppContourLimit.summable_zeroSum hf).norm
  refine h.congr fun ρ => ?_
  rw [norm_mul, Complex.norm_natCast]

theorem summable_sq_unconditional {f : ℝ → ℝ} (hf : IsTestFunction f) :
    Summable (fun ρ : Zero => (zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ ρ : Zero, ‖spectralTransform f ρ‖ ≤ B := by
    refine ⟨∫ u : ℝ, |f u| * Real.exp (|u| / 2), fun ρ => ?_⟩
    exact GppExplicitFormulaE1.norm_spectralTransform_le hf ρ.2.2.1.le ρ.2.2.2.le
  refine Summable.of_nonneg_of_le (fun ρ => by positivity) (fun ρ => ?_)
    ((summable_norm_term hf).mul_left B)
  have hm : (0 : ℝ) ≤ zeroMult ρ := Nat.cast_nonneg _
  have h0 : 0 ≤ ‖spectralTransform f ρ‖ := norm_nonneg _
  have : ‖spectralTransform f ρ‖ ^ 2 ≤ B * ‖spectralTransform f ρ‖ := by
    nlinarith [hB ρ]
  nlinarith [mul_le_mul_of_nonneg_left this hm]

theorem memℓp_amp_unconditional {f : ℝ → ℝ} (hf : IsTestFunction f) : Memℓp (amp f) 2 := by
  refine (memℓp_gen_iff (by simp)).2 ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [norm_amp_sq]
  exact summable_sq_unconditional hf

/-- The state of a test function in `ℓ²(zeros)`, with no hypothesis on the zeros. -/
def stateU (f : Test) : H := ⟨amp f.1, memℓp_amp_unconditional f.2⟩

@[simp] theorem stateU_apply (f : Test) (ρ : Zero) : stateU f ρ = amp f.1 ρ := rfl

/-- Under `OnLine`, the unconditional state is the state of `ZeroHilbertSpace`. -/
theorem stateU_eq_state (hL : OnLine) (f : Test) : stateU f = state hL f := rfl

/-! ## The reflection `ρ ↦ 1 − ρ̄` -/

/-- The zeta involution on the zero set. -/
def iotaZ (ρ : Zero) : Zero :=
  ⟨zetaInvolution ρ, nontrivialZeros_mem_involution ρ.2⟩

@[simp] theorem coe_iotaZ (ρ : Zero) : ((iotaZ ρ : Zero) : ℂ) = 1 - starRingEnd ℂ (ρ : ℂ) := rfl

theorem iotaZ_iotaZ (ρ : Zero) : iotaZ (iotaZ ρ) = ρ :=
  Subtype.ext (zetaInvolution_involutive ρ)

theorem zeroMult_iotaZ (ρ : Zero) : zeroMult ((iotaZ ρ : Zero) : ℂ) = zeroMult (ρ : ℂ) :=
  (zeroData_symmetric ρ.2).2.1

theorem iotaZ_eq_self_iff (ρ : Zero) : iotaZ ρ = ρ ↔ (ρ : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    exact (zetaInvolution_fixed_iff ρ).1 (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((zetaInvolution_fixed_iff ρ).2 h)

/-- The permutation of the zeros. -/
def iotaEquiv : Zero ≃ Zero := Function.Involutive.toPerm iotaZ iotaZ_iotaZ

/-- Reflection of coordinates: `(T x)_ρ = x_{1 - ρ̄}`. -/
def reflectFun (x : H) : Zero → ℂ := fun ρ => x (iotaZ ρ)

theorem memℓp_reflect (x : H) : Memℓp (reflectFun x) 2 := by
  have hx := lp.memℓp x
  refine (memℓp_gen_iff (by simp)).2 ?_
  have h := (memℓp_gen_iff (by simp)).1 hx
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h ⊢
  exact (iotaEquiv.summable_iff.2 h)

def reflect (x : H) : H := ⟨reflectFun x, memℓp_reflect x⟩

@[simp] theorem reflect_apply (x : H) (ρ : Zero) : reflect x ρ = x (iotaZ ρ) := rfl

theorem reflect_reflect (x : H) : reflect (reflect x) = x := by
  ext ρ
  simp [iotaZ_iotaZ]

@[simp] theorem iotaEquiv_apply (ρ : Zero) : iotaEquiv ρ = iotaZ ρ := rfl

theorem inner_reflect_left (x y : H) : inner ℂ (reflect x) y = inner ℂ x (reflect y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  set g : Zero → ℂ := fun ρ => inner ℂ (x ρ) ((reflect y) ρ) with hg
  calc ∑' ρ, inner ℂ ((reflect x) ρ) (y ρ) = ∑' ρ, g (iotaEquiv ρ) := by
        refine tsum_congr fun ρ => ?_
        simp [hg, iotaZ_iotaZ]
    _ = ∑' ρ, g ρ := iotaEquiv.tsum_eq g

/-- `T` is the identity exactly when every zero lies on the critical line. -/
theorem reflect_eq_self_iff_onLine : (∀ x : H, reflect x = x) ↔ OnLine := by
  constructor
  · intro h ρ hρ
    let r : Zero := ⟨ρ, hρ⟩
    by_contra hne
    have hne' : iotaZ r ≠ r := fun e => hne ((iotaZ_eq_self_iff r).1 e)
    have h1 := congrArg (fun x : H => x r) (h (lp.single 2 r (1 : ℂ)))
    simp only [reflect_apply, lp.single_apply, Pi.single_apply, hne', if_false, if_true] at h1
    exact zero_ne_one h1
  · intro hL x
    have : ∀ ρ : Zero, iotaZ ρ = ρ := fun ρ => (iotaZ_eq_self_iff ρ).2 (hL ρ ρ.2)
    ext ρ
    simp [this]

/-! ## The identity -/

theorem amp_term (f : Test) (ρ : Zero) :
    inner ℂ ((reflect (stateU f)) ρ) (stateU f ρ) =
      (zeroMult ρ : ℂ) * spectralTransform (autocorr f.1) ρ := by
  have hm := zeroMult_iotaZ ρ
  rw [GppGwefAssembly.gwef2_factorisation f.2]
  simp only [reflect_apply, stateU_apply, amp, RCLike.inner_apply, hm, map_mul,
    Complex.conj_ofReal]
  have hcj : (starRingEnd ℂ) (spectralTransform f.1 ((iotaZ ρ : Zero) : ℂ)) =
      spectralTransform f.1 (1 - (ρ : ℂ)) := by
    rw [← GppGwefAssembly.spectralTransform_conj, coe_iotaZ, map_sub, map_one,
      Complex.conj_conj]
  rw [hcj]
  have hs : ((Real.sqrt (zeroMult ρ) : ℝ) : ℂ) * ((Real.sqrt (zeroMult ρ) : ℝ) : ℂ) =
      (zeroMult ρ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  linear_combination (spectralTransform f.1 (1 - (ρ : ℂ)) * spectralTransform f.1 ρ) * hs

/-- **Krein-type identity, unconditional.** `weilForm (autocorr f) = ⟨T (S f), S f⟩` on
`ℓ²(zeros)`, with `T` the reflection `ρ ↦ 1 − ρ̄`. No hypothesis on the zeros is used. -/
theorem weilForm_autocorr_eq_inner_reflect (f : Test) :
    inner ℂ (reflect (stateU f)) (stateU f) = (weilForm (autocorr f.1) : ℂ) := by
  rw [lp.inner_eq_tsum]
  rw [tsum_congr (amp_term f)]
  exact (GppExplicitFormulaAssembly.explicit_formula_zeroSum f.2).2

/-- The same identity with the reflection on the right (`T` is self-adjoint). -/
theorem weilForm_autocorr_eq_inner_reflect' (f : Test) :
    inner ℂ (stateU f) (reflect (stateU f)) = (weilForm (autocorr f.1) : ℂ) := by
  rw [← inner_reflect_left, weilForm_autocorr_eq_inner_reflect]

/-- Under `OnLine` the reflection is the identity and the identity is `inner_state_self`. -/
theorem krein_identity_online (hL : OnLine) (f : Test) :
    inner ℂ (reflect (stateU f)) (stateU f) = inner ℂ (state hL f) (state hL f) := by
  rw [weilForm_autocorr_eq_inner_reflect, inner_state_self hL f]

/-! ## Coordinatewise exactness -/

/-- Some test function has a nonzero transform at any given point. -/
theorem exists_test_ne_zero (s : ℂ) : ∃ g : ℝ → ℝ, IsTestFunction g ∧ spectralTransform g s ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hloc : LocallyIntegrable (fun u : ℝ => Complex.exp ((s - 1 / 2) * (u : ℂ))) volume :=
    (by fun_prop : Continuous fun u : ℝ => Complex.exp ((s - 1 / 2) * (u : ℂ))).locallyIntegrable
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hs => by
    have := hcon g ⟨hg, hs⟩
    simpa [spectralTransform, Complex.real_smul] using this)
  obtain ⟨u, hu⟩ := hz.exists
  exact Complex.exp_ne_zero _ hu

/-- The Krein term and the norm term at a single zero. -/
def kreinTerm (f : Test) (ρ : Zero) : ℂ := inner ℂ ((reflect (stateU f)) ρ) (stateU f ρ)

def normTerm (f : Test) (ρ : Zero) : ℂ := inner ℂ (stateU f ρ) (stateU f ρ)

theorem kreinTerm_eq (f : Test) (ρ : Zero) :
    kreinTerm f ρ = (zeroMult ρ : ℂ) * (spectralTransform f.1 ρ * spectralTransform f.1 (1 - ρ)) := by
  rw [kreinTerm, amp_term, GppGwefAssembly.gwef2_factorisation f.2]

theorem normTerm_eq (f : Test) (ρ : Zero) :
    normTerm f ρ = (zeroMult ρ : ℂ) * (spectralTransform f.1 ρ * spectralTransform f.1 (starRingEnd ℂ ρ)) := by
  have hs : ((Real.sqrt (zeroMult ρ) : ℝ) : ℂ) * ((Real.sqrt (zeroMult ρ) : ℝ) : ℂ) = (zeroMult ρ : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]; simp
  simp only [normTerm, stateU_apply, amp, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  rw [← GppGwefAssembly.spectralTransform_conj]
  linear_combination (spectralTransform f.1 ρ * spectralTransform f.1 (starRingEnd ℂ ρ)) * hs

/-- **Coordinatewise exactness.** At a zero `ρ`, the Krein term of `f` equals the norm term of
`f` for every test function exactly when `ρ` is on the critical line. No hypothesis on the other
zeros is used. -/
theorem coordinate_norm_eq_iff (ρ : Zero) :
    (∀ f : Test, kreinTerm f ρ = normTerm f ρ) ↔ (ρ : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    obtain ⟨g, hg, hne⟩ := exists_test_ne_zero (ρ : ℂ)
    let G : Test := ⟨g, hg⟩
    have hm : (zeroMult ρ : ℂ) ≠ 0 := by
      have := one_le_zeroMult ρ.2
      exact_mod_cast (by omega : zeroMult (ρ : ℂ) ≠ 0)
    -- the relation for every translate of `g`
    have key : ∀ t : ℝ, spectralTransform g (1 - (ρ : ℂ)) * Complex.exp (((1 - (ρ : ℂ)) - 1 / 2) * t) =
        spectralTransform g (starRingEnd ℂ ρ) * Complex.exp (((starRingEnd ℂ (ρ : ℂ)) - 1 / 2) * t) := by
      intro t
      have ht := h ⟨shift t g, isTestFunction_shift t hg⟩
      rw [kreinTerm_eq, normTerm_eq] at ht
      simp only [spectralTransform_shift] at ht
      have hρ : Complex.exp (((ρ : ℂ) - 1 / 2) * t) ≠ 0 := Complex.exp_ne_zero _
      have h2 := mul_left_cancel₀ hm ht
      have h3 : Complex.exp (((ρ : ℂ) - 1 / 2) * t) * spectralTransform g ρ ≠ 0 := mul_ne_zero hρ hne
      have h4 := mul_left_cancel₀ h3 h2
      linear_combination h4
    have h0 := key 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    have hA : spectralTransform g (starRingEnd ℂ ρ) ≠ 0 := by
      rw [GppGwefAssembly.spectralTransform_conj]
      exact (map_ne_zero _).2 hne
    have hexp : ∀ t : ℝ, Complex.exp (((1 - (ρ : ℂ)) - 1 / 2) * t) =
        Complex.exp (((starRingEnd ℂ (ρ : ℂ)) - 1 / 2) * t) := by
      intro t
      have := key t
      rw [h0] at this
      exact mul_left_cancel₀ hA this
    -- differentiate at 0
    have hd : ∀ c : ℂ, HasDerivAt (fun t : ℝ => Complex.exp (c * t)) c 0 := by
      intro c
      have h1 : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c)
      simpa using h1.cexp
    have hab : ((1 - (ρ : ℂ)) - 1 / 2) = ((starRingEnd ℂ (ρ : ℂ)) - 1 / 2) := by
      have e : (fun t : ℝ => Complex.exp (((1 - (ρ : ℂ)) - 1 / 2) * t)) =
          (fun t : ℝ => Complex.exp (((starRingEnd ℂ (ρ : ℂ)) - 1 / 2) * t)) := funext hexp
      have := (hd ((1 - (ρ : ℂ)) - 1 / 2)).unique (e ▸ hd ((starRingEnd ℂ (ρ : ℂ)) - 1 / 2))
      simpa using this
    have := congrArg Complex.re hab
    simp at this
    linarith
  · intro hre f
    have : iotaZ ρ = ρ := (iotaZ_eq_self_iff ρ).2 hre
    simp only [kreinTerm, normTerm, reflect_apply, this]

end GppKreinZero
