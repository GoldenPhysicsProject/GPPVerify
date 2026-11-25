/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.BTSigmaSpectralTransform
import GppVerify.RiemannHypothesis.ExplicitFormulaAssembly
import GppVerify.RiemannHypothesis.GwefFactorisation
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The zero Hilbert space: a unitary dilation realization of the arithmetic Weil form

Given the hypothesis `OnLine` (every nontrivial zero of `ζ` has real part `1/2`), this file
builds the Hilbert space `ℓ²(nontrivial zeros)` together with

* a linear map `state : Test → ℓ²` from smooth compactly supported log-variable test functions
  whose squared norm is the arithmetic Weil form of the autocorrelation:
  `⟪state f, state f⟫ = weilForm (autocorr f)` (`inner_state_self`), i.e. the prime side plus the
  archimedean term minus the pole term, through the in-tree explicit formula;
* a one-parameter group of unitaries `evolve t` (multiplication by `exp((ρ - 1/2) t)` on the
  `ρ`-th coordinate) with `evolve t (state f) = state (shift t f)` (`evolve_state`): the unitary
  dilation group is the translation of the log variable;
* for every nontrivial zero `ρ` an eigenvector of the whole group,
  `evolve t (e_ρ) = exp((ρ - 1/2) t) • e_ρ`, of modulus-one eigenvalue (`evolve_single`).

## Scope

Every statement takes `OnLine` (every nontrivial zero of `ζ` has real part `1/2`) as a hypothesis.
It is used to make the phases `exp((ρ - 1/2) t)` unimodular and to turn the explicit formula's
zero sum `Σ m_ρ F(ρ) F(1 - ρ)` into the sum of squares `Σ m_ρ |F(ρ)|²`. The index set of the space
is the set of zeros, so the dilation eigenvalues are the zero ordinates by construction, and the
content of the construction is the norm identity linking the prime-side Weil form to the zeros.
Proved here: the group law, unitarity of each `evolve t`, the intertwining with translation and
the eigenvector family. Continuity of `t ↦ evolve t` and Stone's theorem belong to follow-up work.
-/

noncomputable section

open Complex MeasureTheory GppMeyerSpectralWeil GppXiZeroCounting GppWeilCriterion
  GppArithmeticReflection GppBTSigmaSpectralTransform
open scoped ComplexConjugate ENNReal

namespace GppZeroHilbert

/-- The hypothesis under which the space is built: every nontrivial zero lies on `Re = 1/2`. -/
def OnLine : Prop := ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2

/-- `OnLine` is the strip form of Mathlib's `RiemannHypothesis`. -/
theorem onLine_of_riemannHypothesis (h : RiemannHypothesis) : OnLine := by
  intro ρ hρ
  obtain ⟨hz, h0, h1⟩ := hρ
  refine h ρ hz ?_ ?_
  · rintro ⟨n, hn⟩
    have : ρ.re = -2 * ((n : ℝ) + 1) := by rw [hn]; simp
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · rintro rfl
    simp at h1

/-- Nontrivial zeros, as a type. -/
abbrev Zero : Type := ↥nontrivialZeros

/-- Test functions in the log variable. -/
abbrev Test : Type := {f : ℝ → ℝ // IsTestFunction f}

/-- The ambient Hilbert space `ℓ²` of the nontrivial zeros. -/
abbrev H : Type := lp (fun _ : Zero => ℂ) 2

/-- The coordinate of a test function at the zero `ρ`: `√(mult ρ) · Ψ_f(ρ)`. -/
def amp (f : ℝ → ℝ) (ρ : Zero) : ℂ :=
  ((Real.sqrt (zeroMult ρ) : ℝ) : ℂ) * spectralTransform f ρ

/-- On the critical line, the explicit-formula term is `mult · |Ψ_f(ρ)|²`. -/
theorem term_eq {f : ℝ → ℝ} (hf : IsTestFunction f) (hL : OnLine) (ρ : Zero) :
    (zeroMult ρ : ℂ) * spectralTransform (autocorr f) ρ =
      (((zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2 : ℝ) : ℂ) := by
  have hre : (ρ : ℂ).re = 1 / 2 := hL ρ ρ.2
  have h1 : (1 : ℂ) - ρ = conj (ρ : ℂ) := (one_sub_eq_conj_iff _).2 hre
  rw [GppGwefAssembly.gwef2_factorisation hf, h1, ← spectralTransform_conj]
  push_cast
  rw [Complex.mul_conj']

/-- Summability of the squared coordinates. -/
theorem summable_sq {f : ℝ → ℝ} (hf : IsTestFunction f) (hL : OnLine) :
    Summable (fun ρ : Zero => (zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2) := by
  have hs := (GppExplicitFormulaAssembly.explicit_formula_zeroSum hf).1
  have hs' : Summable (fun ρ : Zero => (((zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2 : ℝ) : ℂ)) :=
    hs.congr (fun ρ => term_eq hf hL ρ)
  exact Complex.summable_ofReal.1 hs'

theorem norm_amp_sq (f : ℝ → ℝ) (ρ : Zero) :
    ‖amp f ρ‖ ^ 2 = (zeroMult ρ : ℝ) * ‖spectralTransform f ρ‖ ^ 2 := by
  unfold amp
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg _)]

theorem memℓp_amp {f : ℝ → ℝ} (hf : IsTestFunction f) (hL : OnLine) : Memℓp (amp f) 2 := by
  refine (memℓp_gen_iff (by simp)).2 ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  simp_rw [norm_amp_sq]
  exact summable_sq hf hL

/-- The state of a test function in the zero Hilbert space. -/
def state (hL : OnLine) (f : Test) : H := ⟨amp f.1, memℓp_amp f.2 hL⟩

/-- **Norm identity.** The squared norm of the state of `f` is the arithmetic Weil form of the
autocorrelation of `f`. -/
theorem inner_state_self (hL : OnLine) (f : Test) :
    inner ℂ (state hL f) (state hL f) = (weilForm (autocorr f.1) : ℂ) := by
  rw [lp.inner_eq_tsum]
  have key : ∀ ρ : Zero, inner ℂ ((state hL f) ρ) ((state hL f) ρ) =
      (zeroMult ρ : ℂ) * spectralTransform (autocorr f.1) ρ := by
    intro ρ
    rw [term_eq f.2 hL ρ, RCLike.inner_apply]
    show amp f.1 ρ * conj (amp f.1 ρ) = _
    rw [Complex.mul_conj', ← Complex.ofReal_pow, norm_amp_sq]
  rw [tsum_congr key]
  exact (GppExplicitFormulaAssembly.explicit_formula_zeroSum f.2).2

/-- Consequently the arithmetic Weil form is nonnegative on squares of test functions. -/
theorem weilForm_autocorr_nonneg (hL : OnLine) (f : Test) : 0 ≤ weilForm (autocorr f.1) := by
  have h := inner_state_self hL f
  have h2 : ((weilForm (autocorr f.1) : ℝ) : ℂ) = ((‖state hL f‖ ^ 2 : ℝ) : ℂ) := by
    rw [← h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have := Complex.ofReal_injective h2
  rw [this]; positivity

/-! ## The dilation group -/

/-- Translation of the log variable. -/
def shift (t : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun u => f (u - t)

theorem isTestFunction_shift (t : ℝ) {f : ℝ → ℝ} (hf : IsTestFunction f) :
    IsTestFunction (shift t f) := by
  refine ⟨hf.1.comp (contDiff_id.sub contDiff_const), ?_⟩
  exact hf.2.comp_homeomorph (Homeomorph.subRight t)

/-- Translating the log variable multiplies the transform by `exp((s - 1/2) t)`. -/
theorem spectralTransform_shift (t : ℝ) (f : ℝ → ℝ) (s : ℂ) :
    spectralTransform (shift t f) s = Complex.exp ((s - 1 / 2) * t) * spectralTransform f s := by
  unfold spectralTransform shift
  have : ∀ u : ℝ, (f (u - t) : ℂ) * Complex.exp ((s - 1 / 2) * u) =
      (fun v : ℝ => (f v : ℂ) * Complex.exp ((s - 1 / 2) * (v : ℂ)) * Complex.exp ((s - 1 / 2) * t))
        (u - t) := by
    intro u
    simp only [Complex.ofReal_sub]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp_rw [this]
  rw [MeasureTheory.integral_sub_right_eq_self
      (fun v : ℝ => (f v : ℂ) * Complex.exp ((s - 1 / 2) * (v : ℂ)) * Complex.exp ((s - 1 / 2) * t)) t,
    integral_mul_const, mul_comm]

/-- The phase of the dilation by `t` at the zero `ρ`. -/
def phase (t : ℝ) (ρ : Zero) : ℂ := Complex.exp (((ρ : ℂ) - 1 / 2) * t)

theorem norm_phase (hL : OnLine) (t : ℝ) (ρ : Zero) : ‖phase t ρ‖ = 1 := by
  have hre : (ρ : ℂ).re = 1 / 2 := hL ρ ρ.2
  unfold phase
  rw [Complex.norm_exp]
  simp [hre]

theorem phase_zero (ρ : Zero) : phase 0 ρ = 1 := by simp [phase]

theorem phase_add (s t : ℝ) (ρ : Zero) : phase (s + t) ρ = phase s ρ * phase t ρ := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem memℓp_phase_mul (hL : OnLine) (t : ℝ) (x : H) : Memℓp (fun ρ => phase t ρ * x ρ) 2 := by
  have hx := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by simp)).1 x.2
  refine (memℓp_gen_iff (by simp)).2 ?_
  refine hx.congr (fun ρ => ?_)
  rw [norm_mul, norm_phase hL, one_mul]

/-- Multiplication by the phases, as a map of `ℓ²`. -/
def mulPhase (hL : OnLine) (t : ℝ) (x : H) : H := ⟨fun ρ => phase t ρ * x ρ, memℓp_phase_mul hL t x⟩

theorem mulPhase_apply (hL : OnLine) (t : ℝ) (x : H) (ρ : Zero) :
    mulPhase hL t x ρ = phase t ρ * x ρ := rfl

theorem mulPhase_zero (hL : OnLine) (x : H) : mulPhase hL 0 x = x := by
  ext ρ; rw [mulPhase_apply, phase_zero, one_mul]

theorem mulPhase_add (hL : OnLine) (s t : ℝ) (x : H) :
    mulPhase hL (s + t) x = mulPhase hL s (mulPhase hL t x) := by
  ext ρ; simp only [mulPhase_apply, phase_add, mul_assoc]

theorem norm_mulPhase (hL : OnLine) (t : ℝ) (x : H) : ‖mulPhase hL t x‖ = ‖x‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp), lp.norm_eq_tsum_rpow (by simp)]
  congr 1
  refine tsum_congr (fun ρ => ?_)
  rw [mulPhase_apply, norm_mul, norm_phase hL, one_mul]

/-- **The unitary dilation group** of the zero Hilbert space. -/
def evolve (hL : OnLine) (t : ℝ) : H ≃ₗᵢ[ℂ] H where
  toFun := mulPhase hL t
  invFun := mulPhase hL (-t)
  map_add' x y := by ext ρ; simp [mulPhase_apply, mul_add]
  map_smul' c x := by ext ρ; simp [mulPhase_apply]; ring
  left_inv x := by rw [← mulPhase_add, neg_add_cancel, mulPhase_zero]
  right_inv x := by rw [← mulPhase_add, add_neg_cancel, mulPhase_zero]
  norm_map' x := norm_mulPhase hL t x

@[simp] theorem evolve_apply (hL : OnLine) (t : ℝ) (x : H) (ρ : Zero) :
    evolve hL t x ρ = phase t ρ * x ρ := rfl

theorem evolve_zero (hL : OnLine) (x : H) : evolve hL 0 x = x := mulPhase_zero hL x

theorem evolve_add (hL : OnLine) (s t : ℝ) (x : H) :
    evolve hL (s + t) x = evolve hL s (evolve hL t x) := mulPhase_add hL s t x

/-- **Dilation = translation.** The unitary dilation carries the state of `f` to the state of its
log-variable translate. -/
theorem evolve_state (hL : OnLine) (t : ℝ) (f : Test) :
    evolve hL t (state hL f) = state hL ⟨shift t f.1, isTestFunction_shift t f.2⟩ := by
  ext ρ
  simp only [evolve_apply, state, amp, phase, spectralTransform_shift]
  ring

/-- **Every zero is an eigenstate of the whole dilation group**, with unimodular eigenvalue. -/
theorem evolve_single (hL : OnLine) (ρ : Zero) (t : ℝ) :
    evolve hL t (lp.single 2 ρ (1 : ℂ)) = phase t ρ • lp.single 2 ρ (1 : ℂ) := by
  ext j
  by_cases hj : j = ρ
  · subst hj; simp
  · simp only [evolve_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    have h0 := lp.single_apply_ne (E := fun _ : Zero => ℂ) 2 ρ (1 : ℂ) hj
    rw [h0]; simp

theorem single_ne_zero (ρ : Zero) : (lp.single 2 ρ (1 : ℂ) : H) ≠ 0 := by
  intro h
  have := congrArg (fun x : H => x ρ) h
  simp at this

/-- **Packaged statement.** Under `OnLine` there is a Hilbert space with a unitary dilation group
and a state map from test functions such that the norm is the arithmetic Weil form, the dilation is
log-variable translation, and every nontrivial zero is a unimodular eigenvalue of the group. -/
theorem zero_hilbert_space (hL : OnLine) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K)
      (U : ℝ → (K ≃ₗᵢ[ℂ] K)) (O : Test → K),
      (∀ f, inner ℂ (O f) (O f) = (weilForm (autocorr f.1) : ℂ)) ∧
      (∀ x, U 0 x = x) ∧ (∀ s t x, U (s + t) x = U s (U t x)) ∧
      (∀ t f, U t (O f) = O ⟨shift t f.1, isTestFunction_shift t f.2⟩) ∧
      (∀ ρ : ℂ, ρ ∈ nontrivialZeros → ∃ v : K, v ≠ 0 ∧ ∀ t : ℝ,
        U t v = Complex.exp ((ρ - 1 / 2) * t) • v ∧ ‖Complex.exp ((ρ - 1 / 2) * t)‖ = 1) :=
  ⟨H, inferInstance, inferInstance, evolve hL, state hL, inner_state_self hL, evolve_zero hL,
    evolve_add hL, evolve_state hL, fun ρ hρ =>
      ⟨lp.single 2 (⟨ρ, hρ⟩ : Zero) (1 : ℂ), single_ne_zero ⟨ρ, hρ⟩, fun t =>
        ⟨evolve_single hL ⟨ρ, hρ⟩ t, norm_phase hL t ⟨ρ, hρ⟩⟩⟩⟩

end GppZeroHilbert

#print axioms GppZeroHilbert.onLine_of_riemannHypothesis
#print axioms GppZeroHilbert.inner_state_self
#print axioms GppZeroHilbert.weilForm_autocorr_nonneg
#print axioms GppZeroHilbert.evolve_state
#print axioms GppZeroHilbert.evolve_single
#print axioms GppZeroHilbert.zero_hilbert_space
