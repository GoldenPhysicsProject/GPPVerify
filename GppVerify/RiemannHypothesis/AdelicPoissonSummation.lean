/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicFourierInversion
import GppVerify.Upstream.SchwartzAffinePoisson

/-!
# Adelic Poisson summation on the adelic Schwartz class

Discharges `AdelicPoissonSummation` (`AdelicPoissonStatement.lean`).
-/

open MeasureTheory GppIdeleQ Rat.FiniteAdeleRing
open scoped FourierTransform SchwartzMap

namespace GlobalTate.Poisson

theorem principal_fst (q : ℚ) : (principal q).1 = (q : ℝ) := rfl

theorem principal_snd (q : ℚ) : (principal q).2 = algebraMap ℚ Af q := rfl

/-- The finite part of the standard character on a rational: `ψ_f(q) = 𝐞(-q)`. -/
theorem finChar_algebraMap (q : ℚ) : finChar (algebraMap ℚ Af q) = Real.fourierChar (-(q : ℝ)) := by
  have h := adeleChar_principal q
  rw [show principal q = ((q : ℝ), algebraMap ℚ Af q) from rfl, adeleChar_split] at h
  have h2 : Real.fourierChar (q : ℝ) * Real.fourierChar (-(q : ℝ)) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  exact mul_left_cancel (h.trans h2.symm)

/-- A rational lies in the coset `ρ + N∏ℤ_v` exactly when it is `ρ + N m` with `m ∈ ℤ`. -/
theorem rat_mem_coset_iff {N : ℕ} (hN : N ≠ 0) (ρ q : ℚ) :
    algebraMap ℚ Af q - algebraMap ℚ Af ρ ∈ natMulIntegral N ↔ ∃ m : ℤ, q = ρ + N * m := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have e : algebraMap ℚ Af ((N : ℚ)⁻¹) * (algebraMap ℚ Af q - algebraMap ℚ Af ρ) =
      algebraMap ℚ Af ((N : ℚ)⁻¹ * (q - ρ)) := by
    rw [map_mul, map_sub]
  show algebraMap ℚ Af ((N : ℚ)⁻¹) * (algebraMap ℚ Af q - algebraMap ℚ Af ρ) ∈ integralAdeles ↔ _
  rw [e]
  have h := principal_snd_mem_intBox_iff ((N : ℚ)⁻¹ * (q - ρ))
  rw [principal_snd] at h
  refine h.trans ⟨fun ⟨m, hm⟩ => ⟨m, ?_⟩, fun ⟨m, hm⟩ => ⟨m, ?_⟩⟩
  · field_simp at hm
    linarith
  · rw [hm]; field_simp; ring

/-- A rational lies in `(1/N)∏ℤ_v` exactly when it is `k / N` with `k ∈ ℤ`. -/
theorem rat_mem_integralDivNat_iff {N : ℕ} (hN : N ≠ 0) (y : ℚ) :
    algebraMap ℚ Af y ∈ integralDivNat N ↔ ∃ k : ℤ, y = k / N := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have e : (N : Af) * algebraMap ℚ Af y = algebraMap ℚ Af ((N : ℚ) * y) := by
    rw [map_mul, map_natCast]
  show (N : Af) * algebraMap ℚ Af y ∈ integralAdeles ↔ _
  rw [e]
  have h := principal_snd_mem_intBox_iff ((N : ℚ) * y)
  rw [principal_snd] at h
  refine h.trans ⟨fun ⟨k, hk⟩ => ⟨k, ?_⟩, fun ⟨k, hk⟩ => ⟨k, ?_⟩⟩
  · field_simp; linarith
  · rw [hk]; field_simp

open Classical in
/-- **Adelic Poisson summation for a coset indicator.** -/
theorem poissonSummation_coset (φ : 𝓢(ℝ, ℂ)) {N : ℕ} (hN : N ≠ 0) (ρ : ℚ) :
    PoissonSummationFor (pureTensor φ (cosetIndicator N (algebraMap ℚ Af ρ))) := by
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  obtain ⟨hS1, hS2, hEq⟩ := SchwartzMap.tsum_affineComp_eq_tsum_fourier φ N hN (ρ : ℝ)
  set g := cosetIndicator N (algebraMap ℚ Af ρ) with hg
  -- the position side
  let e : ℤ → ℚ := fun m => ρ + N * m
  have he : Function.Injective e := by
    intro a b h
    have : (N : ℚ) * a = N * b := by simpa [e] using h
    exact_mod_cast mul_left_cancel₀ hN' this
  have hA : ∀ q : ℚ, pureTensor φ g (principal q) =
      if ∃ m : ℤ, q = ρ + N * m then φ (q : ℝ) else 0 := by
    intro q
    simp only [pureTensor, principal_fst, principal_snd, hg, cosetIndicator]
    by_cases h : ∃ m : ℤ, q = ρ + N * m
    · rw [if_pos h, Set.indicator_of_mem
        (show algebraMap ℚ Af q ∈ {y : Af | y - algebraMap ℚ Af ρ ∈ natMulIntegral N} from
          (rat_mem_coset_iff hN ρ q).2 h)]
      simp
    · rw [if_neg h, Set.indicator_of_notMem
        (show algebraMap ℚ Af q ∉ {y : Af | y - algebraMap ℚ Af ρ ∈ natMulIntegral N} from
          fun h' => h ((rat_mem_coset_iff hN ρ q).1 h'))]
      simp
  have hAsupp : ∀ q ∉ Set.range e, pureTensor φ g (principal q) = 0 := by
    intro q hq
    rw [hA, if_neg]
    rintro ⟨m, hm⟩
    exact hq ⟨m, hm.symm⟩
  have hAe : ∀ m : ℤ, pureTensor φ g (principal (e m)) = φ ((ρ : ℝ) + N * m) := by
    intro m
    rw [hA, if_pos ⟨m, rfl⟩]
    simp [e]
  -- the frequency side
  let e' : ℤ → ℚ := fun k => (k : ℚ) / N
  have he' : Function.Injective e' := by
    intro a b h
    have : (a : ℚ) = b := by simpa [e', hN'] using h
    exact_mod_cast this
  have hB : ∀ y : ℚ, adelicFourier (pureTensor φ g) (principal y) =
      if ∃ k : ℤ, y = k / N then
        (((N : ℝ)⁻¹ : ℝ) : ℂ) * (Real.fourierChar (ρ * y) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) (y : ℝ)
      else 0 := by
    intro y
    rw [show principal y = ((y : ℝ), algebraMap ℚ Af y) from rfl, adelicFourier_pureTensor,
      hg, finFourier_cosetIndicator hN]
    have hF : (𝓕 (φ : ℝ → ℂ)) (y : ℝ) = (𝓕 φ : 𝓢(ℝ, ℂ)) (y : ℝ) := rfl
    rw [hF]
    by_cases h : ∃ k : ℤ, y = k / N
    · rw [if_pos h, Set.indicator_of_mem ((rat_mem_integralDivNat_iff hN y).2 h)]
      have hc : ψc (-(algebraMap ℚ Af ρ * algebraMap ℚ Af y)) = Real.fourierChar ((ρ : ℝ) * y) := by
        rw [ψc, ← map_mul, ← map_neg, finChar_algebraMap]
        push_cast
        simp
      rw [hc]
      push_cast
      simp
      ring
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h ((rat_mem_integralDivNat_iff hN y).1 h'))]
      simp
  have hBsupp : ∀ y ∉ Set.range e', adelicFourier (pureTensor φ g) (principal y) = 0 := by
    intro y hy
    rw [hB, if_neg]
    rintro ⟨k, hk⟩
    exact hy ⟨k, hk.symm⟩
  have hBe : ∀ k : ℤ, adelicFourier (pureTensor φ g) (principal (e' k)) =
      (((N : ℝ)⁻¹ : ℝ) : ℂ) * (Real.fourierChar ((ρ : ℝ) * k / N) : ℂ) * (𝓕 φ : 𝓢(ℝ, ℂ)) ((k : ℝ) / N) := by
    intro k
    rw [hB, if_pos ⟨k, rfl⟩]
    have h1 : (((e' k : ℚ)) : ℝ) = (k : ℝ) / N := by simp [e']
    rw [h1, ← mul_div_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← he.summable_iff hAsupp]
    simpa [Function.comp_def, hAe] using hS1
  · rw [← he'.summable_iff hBsupp]
    simpa [Function.comp_def, hBe] using hS2
  · have hsA : Function.support (fun q : ℚ => pureTensor φ g (principal q)) ⊆ Set.range e :=
      fun q hq => by_contra fun h => hq (hAsupp q h)
    have hsB : Function.support (fun y : ℚ => adelicFourier (pureTensor φ g) (principal y)) ⊆
        Set.range e' := fun y hy => by_contra fun h => hy (hBsupp y h)
    rw [← he.tsum_eq hsA, ← he'.tsum_eq hsB]
    simp only [hAe, hBe]
    exact hEq

/-! ### Closure under linear combinations -/

theorem poissonSummationFor_zero : PoissonSummationFor (0 : AQ → ℂ) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using summable_zero
  · have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
    simp [this]
  · have : adelicFourier (0 : AQ → ℂ) = 0 := funext adelicFourier_zero
    simp [this]

theorem poissonSummationFor_add {f g : AQ → ℂ} (hf : AdelicGood f) (hg : AdelicGood g)
    (pf : PoissonSummationFor f) (pg : PoissonSummationFor g) : PoissonSummationFor (f + g) := by
  obtain ⟨a1, a2, a3⟩ := pf
  obtain ⟨b1, b2, b3⟩ := pg
  have hF : adelicFourier (f + g) = adelicFourier f + adelicFourier g :=
    funext fun y => adelicFourier_add hf hg y
  refine ⟨a1.add b1, ?_, ?_⟩
  · simpa [hF] using a2.add b2
  · simp only [hF, Pi.add_apply]
    rw [a1.tsum_add b1, a2.tsum_add b2, a3, b3]

theorem poissonSummationFor_smul (k : ℂ) {f : AQ → ℂ} (pf : PoissonSummationFor f) :
    PoissonSummationFor (k • f) := by
  obtain ⟨a1, a2, a3⟩ := pf
  have hF : adelicFourier (k • f) = k • adelicFourier f :=
    funext fun y => adelicFourier_smul k f y
  refine ⟨by simpa using a1.const_smul k, ?_, ?_⟩
  · simpa [hF] using a2.const_smul k
  · simp only [hF, Pi.smul_apply, smul_eq_mul]
    rw [tsum_mul_left, tsum_mul_left, a3]

/-! ### The whole class -/

theorem exists_rat_sub_mem_natMulIntegral {N : ℕ} (hN : N ≠ 0) (a : Af) :
    ∃ ρ : ℚ, a - algebraMap ℚ Af ρ ∈ natMulIntegral N := by
  obtain ⟨q, hq⟩ := exists_rat_sub_mem_integralAdeles' a
  obtain ⟨s, -, hs⟩ := exists_natCast_sub_mem_natMulIntegral hN hq
  refine ⟨q + s, ?_⟩
  have : a - algebraMap ℚ Af (q + s) = (a - algebraMap ℚ Af q) - (s : Af) := by
    rw [map_add, map_natCast]; ring
  rw [this]; exact hs

theorem cosetIndicator_eq_of_sub_mem {N : ℕ} {a b : Af} (h : a - b ∈ natMulIntegral N) :
    cosetIndicator N a = cosetIndicator N b := by
  unfold cosetIndicator
  congr 1
  ext y
  simp only [Set.mem_ofPred_eq]
  constructor
  · intro hy
    have e : y - b = (y - a) + (a - b) := by ring
    rw [e]; exact add_mem_natMulIntegral hy h
  · intro hy
    have e : y - a = (y - b) - (a - b) := by ring
    rw [e]; exact sub_mem_natMulIntegral hy h

theorem adelicGood_pureTensor_of (φ : 𝓢(ℝ, ℂ)) {g : Af → ℂ} (hg : Integrable g haar)
    (hb : ∃ C : ℝ, ∀ b, ‖g b‖ ≤ C) : AdelicGood (pureTensor φ g) := by
  refine ⟨φ.integrable.mul_prod hg, ?_⟩
  obtain ⟨C, hC⟩ := hb
  refine ⟨(SchwartzMap.seminorm ℂ 0 0 φ) * C, fun x => ?_⟩
  simp only [pureTensor, norm_mul]
  exact mul_le_mul (by simpa using SchwartzMap.norm_le_seminorm ℂ φ x.1) (hC x.2)
    (norm_nonneg _) (by positivity)

theorem cosetIndicator_norm_le {N : ℕ} (a b : Af) : ‖cosetIndicator N a b‖ ≤ 1 := by
  by_cases h : b ∈ {y : Af | y - a ∈ natMulIntegral N} <;> simp [cosetIndicator, h]

/-- **Adelic Poisson summation for a pure tensor `φ ⊗ g`** with `g` Schwartz–Bruhat. -/
theorem poissonSummation_pureTensor_sb (φ : 𝓢(ℝ, ℂ)) {g : Af → ℂ} (hg : IsSchwartzBruhat g) :
    PoissonSummationFor (pureTensor φ g) := by
  classical
  obtain ⟨N, hN, huni⟩ := exists_uniform_of_isLocallyConstant hg.1 hg.2
  obtain ⟨F, hF⟩ := exists_expansion hg.2 huni
  have hsum : pureTensor φ g = ∑ cl ∈ F, (g cl.out) • pureTensor φ (cosetIndicator N cl.out) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pureTensor]
    rw [hF x.2, Finset.mul_sum]
    exact Finset.sum_congr rfl fun cl _ => by ring
  have key : ∀ cl ∈ F, AdelicGood ((g cl.out) • pureTensor φ (cosetIndicator N cl.out)) ∧
      PoissonSummationFor ((g cl.out) • pureTensor φ (cosetIndicator N cl.out)) := by
    intro cl _
    obtain ⟨ρ, hρ⟩ := exists_rat_sub_mem_natMulIntegral hN cl.out
    have hc : cosetIndicator N cl.out = cosetIndicator N (algebraMap ℚ Af ρ) :=
      cosetIndicator_eq_of_sub_mem hρ
    have hgood : AdelicGood (pureTensor φ (cosetIndicator N cl.out)) :=
      adelicGood_pureTensor_of φ (integrable_cosetIndicator hN _)
        ⟨1, cosetIndicator_norm_le _⟩
    refine ⟨hgood.smul _, poissonSummationFor_smul _ ?_⟩
    rw [hc]
    exact poissonSummation_coset φ hN ρ
  rw [hsum]
  refine (Finset.sum_induction _ (fun f : AQ → ℂ => AdelicGood f ∧ PoissonSummationFor f)
    (fun f g hf hg => ⟨hf.1.add hg.1, poissonSummationFor_add hf.1 hg.1 hf.2 hg.2⟩)
    ⟨AdelicGood.zero, poissonSummationFor_zero⟩ key).2

/-- **Adelic Poisson summation on the adelic Schwartz class**: `AdelicPoissonSummation`. -/
theorem adelicPoissonSummation : AdelicPoissonSummation := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, g, hg, rfl⟩ := hf
    exact poissonSummation_pureTensor_sb φ hg
  | zero => exact poissonSummationFor_zero
  | add f g hfm hgm hf hg =>
    exact poissonSummationFor_add (adelicGood_of_mem hfm) (adelicGood_of_mem hgm) hf hg
  | smul k f hfm hf => exact poissonSummationFor_smul k hf

end GlobalTate.Poisson
