/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicFiniteFourier

/-!
# Fourier inversion and Plancherel on the adelic Schwartz class

Discharges `AdelicFourierInversion` and `AdelicPlancherel` (`AdelicPoissonStatement.lean`).
-/

open MeasureTheory GppIdeleQ Rat.FiniteAdeleRing
open scoped FourierTransform SchwartzMap ComplexConjugate

namespace GlobalTate.Poisson

/-- Integrable and bounded. -/
def AdelicGood (f : AQ → ℂ) : Prop :=
  Integrable f adeleHaar ∧ ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C

theorem AdelicGood.zero : AdelicGood 0 :=
  ⟨integrable_zero _ _ _, 0, fun _ => by simp⟩

theorem AdelicGood.add {f g : AQ → ℂ} (hf : AdelicGood f) (hg : AdelicGood g) :
    AdelicGood (f + g) := by
  obtain ⟨hf1, C, hC⟩ := hf
  obtain ⟨hg1, D, hD⟩ := hg
  exact ⟨hf1.add hg1, C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

theorem AdelicGood.smul {f : AQ → ℂ} (k : ℂ) (hf : AdelicGood f) : AdelicGood (k • f) := by
  obtain ⟨hf1, C, hC⟩ := hf
  refine ⟨hf1.smul k, ‖k‖ * C, fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

theorem IsSchwartzBruhat.integrable {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    Integrable g haar := hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem IsSchwartzBruhat.bounded {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    ∃ C : ℝ, ∀ b, ‖g b‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  exact ⟨C, hC⟩

theorem adelicGood_pureTensor (φ : 𝓢(ℝ, ℂ)) {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    AdelicGood (pureTensor φ g) := by
  refine ⟨?_, ?_⟩
  · exact φ.integrable.mul_prod hg.integrable
  · obtain ⟨C, hC⟩ := hg.bounded
    refine ⟨(SchwartzMap.seminorm ℂ 0 0 φ) * C, fun x => ?_⟩
    simp only [pureTensor, norm_mul]
    exact mul_le_mul (by simpa using SchwartzMap.norm_le_seminorm ℂ φ x.1) (hC x.2)
      (norm_nonneg _) (by positivity)

theorem adelicGood_of_mem {f : AQ → ℂ} (hf : f ∈ AdelicSchwartz) : AdelicGood f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, g, hg, rfl⟩ := hf
    exact adelicGood_pureTensor φ hg
  | zero => exact AdelicGood.zero
  | add f g _ _ hf hg => exact hf.add hg
  | smul k f _ hf => exact hf.smul k

/-! ### Linearity of the transform on good functions -/

theorem continuous_kernel (y : AQ) : Continuous fun x : AQ => (adeleChar (-(x * y)) : ℂ) :=
  continuous_subtype_val.comp (continuous_adeleChar.comp (continuous_id.mul continuous_const).neg)

theorem AdelicGood.integrable_kernel {f : AQ → ℂ} (hf : AdelicGood f) (y : AQ) :
    Integrable (fun x => (adeleChar (-(x * y)) : ℂ) * f x) adeleHaar :=
  hf.1.bdd_mul (c := 1) (continuous_kernel y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Circle.norm_coe _).le)

theorem adelicFourier_add {f g : AQ → ℂ} (hf : AdelicGood f) (hg : AdelicGood g) (y : AQ) :
    adelicFourier (f + g) y = adelicFourier f y + adelicFourier g y := by
  unfold adelicFourier
  simp_rw [Pi.add_apply, mul_add]
  exact integral_add (hf.integrable_kernel y) (hg.integrable_kernel y)

theorem adelicFourier_smul (k : ℂ) (f : AQ → ℂ) (y : AQ) :
    adelicFourier (k • f) y = k * adelicFourier f y := by
  unfold adelicFourier
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_left_comm _ k, integral_const_mul]

theorem adelicFourier_zero (y : AQ) : adelicFourier (0 : AQ → ℂ) y = 0 := by
  simp [adelicFourier]

/-- The transform of a pure tensor is the pure tensor of the transforms. -/
theorem adelicFourier_pureTensor_eq (φ : 𝓢(ℝ, ℂ)) (g : Af → ℂ) :
    adelicFourier (pureTensor φ g) = pureTensor (𝓕 φ) (finFourier g) := by
  funext ⟨y, b⟩
  rw [adelicFourier_pureTensor]
  rfl

/-- The transform preserves the adelic Schwartz class. -/
theorem adelicFourier_mem {f : AQ → ℂ} (hf : f ∈ AdelicSchwartz) :
    adelicFourier f ∈ AdelicSchwartz := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, g, hg, rfl⟩ := hf
    rw [adelicFourier_pureTensor_eq]
    exact pureTensor_mem (isSchwartzBruhat_finFourier hg)
  | zero =>
    have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
    rw [this]; exact Submodule.zero_mem _
  | add f g hfm hgm hf hg =>
    have : adelicFourier (f + g) = adelicFourier f + adelicFourier g :=
      funext fun y => adelicFourier_add (adelicGood_of_mem hfm) (adelicGood_of_mem hgm) y
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul k f hfm hf =>
    have : adelicFourier (k • f) = k • adelicFourier f :=
      funext fun y => adelicFourier_smul k f y
    rw [this]; exact Submodule.smul_mem _ k hf

/-- **Fourier inversion on the adelic Schwartz class**: `AdelicFourierInversion`. -/
theorem adelicFourierInversion : AdelicFourierInversion := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, g, hg, rfl⟩ := hf
    intro x
    obtain ⟨y, b⟩ := x
    rw [adelicFourier_pureTensor_eq, adelicFourier_pureTensor_eq]
    show 𝓕 (𝓕 φ) y * finFourier (finFourier g) b = φ (-y) * g (-b)
    rw [finFourier_finFourier_schwartzBruhat hg]
    congr 1
    have h := congrFun (φ.continuous.fourierInv_fourier_eq φ.integrable (𝓕 φ).integrable) (-y)
    rw [Real.fourierInv_eq_fourier_neg, neg_neg] at h
    exact h
  | zero =>
    intro x
    have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
    rw [this]; simp [adelicFourier_zero]
  | add f g hfm hgm hf hg =>
    intro x
    have h1 : adelicFourier (f + g) = adelicFourier f + adelicFourier g :=
      funext fun y => adelicFourier_add (adelicGood_of_mem hfm) (adelicGood_of_mem hgm) y
    rw [h1, adelicFourier_add (adelicGood_of_mem (adelicFourier_mem hfm))
      (adelicGood_of_mem (adelicFourier_mem hgm)), hf x, hg x]
    rfl
  | smul k f hfm hf =>
    intro x
    have h1 : adelicFourier (k • f) = k • adelicFourier f :=
      funext fun y => adelicFourier_smul k f y
    rw [h1, adelicFourier_smul]
    show k * adelicFourier (adelicFourier f) x = k * f (-x)
    rw [hf x]

/-! ### Plancherel -/

/-- The pairing `⟨f, g⟩ = ∫ conj f · g` against `adeleHaar`. -/
noncomputable def adelicPair (f g : AQ → ℂ) : ℂ := ∫ x, conj (f x) * g x ∂adeleHaar

theorem AdelicGood.integrable_conj_mul {f g : AQ → ℂ} (hf : AdelicGood f) (hg : AdelicGood g) :
    Integrable (fun x => conj (f x) * g x) adeleHaar := by
  obtain ⟨hf1, C, hC⟩ := hf
  refine hg.1.bdd_mul (c := C) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact Complex.continuous_conj.comp_aestronglyMeasurable hf1.aestronglyMeasurable
  · simpa using hC x

theorem adelicPair_add_left {f f' g : AQ → ℂ} (hf : AdelicGood f) (hf' : AdelicGood f')
    (hg : AdelicGood g) : adelicPair (f + f') g = adelicPair f g + adelicPair f' g := by
  unfold adelicPair
  simp_rw [Pi.add_apply, map_add, add_mul]
  exact integral_add (hf.integrable_conj_mul hg) (hf'.integrable_conj_mul hg)

theorem adelicPair_add_right {f g g' : AQ → ℂ} (hf : AdelicGood f) (hg : AdelicGood g)
    (hg' : AdelicGood g') : adelicPair f (g + g') = adelicPair f g + adelicPair f g' := by
  unfold adelicPair
  simp_rw [Pi.add_apply, mul_add]
  exact integral_add (hf.integrable_conj_mul hg) (hf.integrable_conj_mul hg')

theorem adelicPair_smul_left (k : ℂ) (f g : AQ → ℂ) :
    adelicPair (k • f) g = conj k * adelicPair f g := by
  unfold adelicPair
  simp_rw [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, integral_const_mul]

theorem adelicPair_smul_right (k : ℂ) (f g : AQ → ℂ) :
    adelicPair f (k • g) = k * adelicPair f g := by
  unfold adelicPair
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_left_comm _ k, integral_const_mul]

theorem adelicPair_zero_left (g : AQ → ℂ) : adelicPair 0 g = 0 := by simp [adelicPair]

theorem adelicPair_zero_right (f : AQ → ℂ) : adelicPair f 0 = 0 := by simp [adelicPair]

/-- Pairing of pure tensors factorizes. -/
theorem adelicPair_pureTensor (φ ψ : 𝓢(ℝ, ℂ)) (g h : Af → ℂ) :
    adelicPair (pureTensor φ g) (pureTensor ψ h) =
      (∫ x : ℝ, conj (φ x) * ψ x) * ∫ b : Af, conj (g b) * h b ∂haar := by
  unfold adelicPair adeleHaar
  have key : ∀ x : AQ, conj (pureTensor φ g x) * pureTensor ψ h x =
      (conj (φ x.1) * ψ x.1) * (conj (g x.2) * h x.2) := by
    intro x; simp only [pureTensor, map_mul]; ring
  simp_rw [key]
  exact integral_prod_mul (fun x : ℝ => conj (φ x) * ψ x) (fun b : Af => conj (g b) * h b)

/-- Plancherel on the line (Mathlib), in the form used here. -/
theorem integral_conj_fourier_fourier (φ ψ : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, conj ((𝓕 φ : 𝓢(ℝ, ℂ)) x) * (𝓕 ψ : 𝓢(ℝ, ℂ)) x = ∫ x : ℝ, conj (φ x) * ψ x := by
  have h := SchwartzMap.integral_inner_fourier_fourier φ ψ
  simpa [inner, mul_comm] using h

theorem adelicPair_fourier_pureTensor (φ ψ : 𝓢(ℝ, ℂ)) {g h : Af → ℂ}
    (hg : IsSchwartzBruhat g) (hh : IsSchwartzBruhat h) :
    adelicPair (adelicFourier (pureTensor φ g)) (adelicFourier (pureTensor ψ h)) =
      adelicPair (pureTensor φ g) (pureTensor ψ h) := by
  rw [adelicFourier_pureTensor_eq, adelicFourier_pureTensor_eq, adelicPair_pureTensor,
    adelicPair_pureTensor, integral_conj_fourier_fourier, finParseval hg hh]

/-- **Parseval on the adelic Schwartz class.** -/
theorem adelicPair_fourier {f g : AQ → ℂ} (hf : f ∈ AdelicSchwartz) (hg : g ∈ AdelicSchwartz) :
    adelicPair (adelicFourier f) (adelicFourier g) = adelicPair f g := by
  -- first, against a pure tensor in the second slot
  have step : ∀ (ψ : 𝓢(ℝ, ℂ)) (h : Af → ℂ), IsSchwartzBruhat h → ∀ f ∈ AdelicSchwartz,
      adelicPair (adelicFourier f) (adelicFourier (pureTensor ψ h)) =
        adelicPair f (pureTensor ψ h) := by
    intro ψ h hh f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨φ, g, hg, rfl⟩ := hf
      exact adelicPair_fourier_pureTensor φ ψ hg hh
    | zero =>
      have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
      rw [this, adelicPair_zero_left, adelicPair_zero_left]
    | add f f' hfm hfm' hf hf' =>
      have h1 : adelicFourier (f + f') = adelicFourier f + adelicFourier f' :=
        funext fun y => adelicFourier_add (adelicGood_of_mem hfm) (adelicGood_of_mem hfm') y
      have hG := adelicGood_of_mem (adelicFourier_mem (pureTensor_mem hh (φ := ψ)))
      rw [h1, adelicPair_add_left (adelicGood_of_mem (adelicFourier_mem hfm))
        (adelicGood_of_mem (adelicFourier_mem hfm')) hG,
        adelicPair_add_left (adelicGood_of_mem hfm) (adelicGood_of_mem hfm')
          (adelicGood_pureTensor ψ hh), hf, hf']
    | smul k f hfm hf =>
      have h1 : adelicFourier (k • f) = k • adelicFourier f :=
        funext fun y => adelicFourier_smul k f y
      rw [h1, adelicPair_smul_left, adelicPair_smul_left, hf]
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨ψ, h, hh, rfl⟩ := hg
    exact step ψ h hh f hf
  | zero =>
    have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
    rw [this, adelicPair_zero_right, adelicPair_zero_right]
  | add g g' hgm hgm' hg hg' =>
    have h1 : adelicFourier (g + g') = adelicFourier g + adelicFourier g' :=
      funext fun y => adelicFourier_add (adelicGood_of_mem hgm) (adelicGood_of_mem hgm') y
    rw [h1, adelicPair_add_right (adelicGood_of_mem (adelicFourier_mem hf))
      (adelicGood_of_mem (adelicFourier_mem hgm)) (adelicGood_of_mem (adelicFourier_mem hgm')),
      adelicPair_add_right (adelicGood_of_mem hf) (adelicGood_of_mem hgm) (adelicGood_of_mem hgm'),
      hg, hg']
  | smul k g hgm hg =>
    have h1 : adelicFourier (k • g) = k • adelicFourier g :=
      funext fun y => adelicFourier_smul k g y
    rw [h1, adelicPair_smul_right, adelicPair_smul_right, hg]

/-- **Plancherel on the adelic Schwartz class**: `AdelicPlancherel`. -/
theorem adelicPlancherel : AdelicPlancherel := by
  intro f hf
  have h := adelicPair_fourier hf hf
  have key : ∀ F : AQ → ℂ, adelicPair F F = ((∫ x, ‖F x‖ ^ 2 ∂adeleHaar : ℝ) : ℂ) := by
    intro F
    unfold adelicPair
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [Complex.conj_mul']
  rw [key, key] at h
  exact_mod_cast h

end GlobalTate.Poisson
