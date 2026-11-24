/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.RiemannHypothesis.AdelicPoissonSummation
import GppVerify.RiemannHypothesis.AdelicHaarScaling

/-!
# The idele-scaled Poisson formula

Discharges `AdelicPoissonScaled` (GZ5): `∑ f(a q) = |a|⁻¹ ∑ 𝓕f(a⁻¹ q)`.

* `dilate a f`: `x ↦ f(a x)`.
* `dilate_mem`: the adelic Schwartz class is stable under dilation by an idele.
* `adelicFourier_dilate`: `𝓕(f(a ·))(y) = |a|⁻¹ 𝓕f(a⁻¹ y)`, from `haarScaling`.
-/

open MeasureTheory GppIdeleQ Rat.FiniteAdeleRing
open scoped FourierTransform SchwartzMap

namespace GlobalTate.Poisson

/-- Dilation by an idele. -/
noncomputable def dilate (a : Idele) (f : AQ → ℂ) : AQ → ℂ := fun x => f (ideleToAdele a * x)

theorem ideleToAdele_mul (a b : Idele) : ideleToAdele (a * b) = ideleToAdele a * ideleToAdele b := by
  ext <;> simp [ideleToAdele]

theorem ideleToAdele_one : ideleToAdele 1 = 1 := by ext <;> simp [ideleToAdele]

/-- Multiplication by an idele, as a homeomorphism of `AQ`. -/
noncomputable def ideleHomeo (a : Idele) : AQ ≃ₜ AQ where
  toFun x := ideleToAdele a * x
  invFun x := ideleToAdele a⁻¹ * x
  left_inv x := by show _ * (_ * x) = x; rw [← mul_assoc, ← ideleToAdele_mul, inv_mul_cancel, ideleToAdele_one, one_mul]
  right_inv x := by show _ * (_ * x) = x; rw [← mul_assoc, ← ideleToAdele_mul, mul_inv_cancel, ideleToAdele_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

theorem ideleHomeo_apply (a : Idele) (x : AQ) : ideleHomeo a x = ideleToAdele a * x := rfl

theorem ideleNorm_nonneg (a : Idele) : 0 ≤ ideleNorm a :=
  mul_nonneg (abs_nonneg _) (finNorm_nonneg _)

theorem ideleToAdele_mul_inv (a : Idele) : ideleToAdele a * ideleToAdele a⁻¹ = 1 := by
  rw [← ideleToAdele_mul, mul_inv_cancel, ideleToAdele_one]

/-- **The transform of a dilate**: `𝓕(f(a ·))(y) = |a|⁻¹ 𝓕f(a⁻¹ y)`. -/
theorem adelicFourier_dilate (a : Idele) (f : AQ → ℂ) (y : AQ) :
    adelicFourier (dilate a f) y =
      (((ideleNorm a)⁻¹ : ℝ) : ℂ) * adelicFourier f (ideleToAdele a⁻¹ * y) := by
  unfold adelicFourier dilate
  set H : AQ → ℂ := fun z => (adeleChar (-(z * (ideleToAdele a⁻¹ * y))) : ℂ) * f z with hH
  have h1 : ∀ x : AQ, (adeleChar (-(x * y)) : ℂ) * f (ideleToAdele a * x) =
      H (ideleHomeo a x) := by
    intro x
    simp only [hH, ideleHomeo_apply]
    have : ideleToAdele a * x * (ideleToAdele a⁻¹ * y) = x * y := by
      calc ideleToAdele a * x * (ideleToAdele a⁻¹ * y)
          = (ideleToAdele a * ideleToAdele a⁻¹) * (x * y) := by ring
        _ = x * y := by rw [ideleToAdele_mul_inv, one_mul]
    rw [this]
  simp_rw [h1]
  have hme : MeasurableEmbedding (ideleHomeo a) := (ideleHomeo a).measurableEmbedding
  rw [← hme.integral_map]
  have hmap : adeleHaar.map (ideleHomeo a) =
      ENNReal.ofReal (ideleNorm a)⁻¹ • adeleHaar := haarScaling a
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 (ideleNorm_nonneg a)),
    Complex.real_smul]

theorem dilate_add (a : Idele) (f g : AQ → ℂ) : dilate a (f + g) = dilate a f + dilate a g := rfl

theorem dilate_smul (a : Idele) (k : ℂ) (f : AQ → ℂ) : dilate a (k • f) = k • dilate a f := rfl

/-- Multiplication by a finite idele preserves the Schwartz–Bruhat class. -/
theorem IsSchwartzBruhat.comp_mul {g : Af → ℂ} (hg : IsSchwartzBruhat g) (u : Afˣ) :
    IsSchwartzBruhat (fun b => g ((u : Af) * b)) := by
  refine ⟨hg.1.comp_continuous (mulHomeo u).continuous, ?_⟩
  exact hg.2.comp_homeomorph (mulHomeo u)

/-- The dilate of a pure tensor is a pure tensor. -/
theorem dilate_pureTensor (a : Idele) (φ : 𝓢(ℝ, ℂ)) (g : Af → ℂ) :
    dilate a (pureTensor φ g) =
      pureTensor (SchwartzMap.affineComp φ (a.1 : ℝ) a.1.ne_zero 0) (fun b => g ((a.2 : Af) * b)) := by
  funext x
  simp [dilate, pureTensor, ideleToAdele, SchwartzMap.affineComp_apply]

/-- **The adelic Schwartz class is stable under dilation by an idele.** -/
theorem dilate_mem (a : Idele) {f : AQ → ℂ} (hf : f ∈ AdelicSchwartz) :
    dilate a f ∈ AdelicSchwartz := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨φ, g, hg, rfl⟩ := hf
    rw [dilate_pureTensor]
    exact pureTensor_mem (hg.comp_mul a.2)
  | zero => exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [dilate_add]; exact Submodule.add_mem _ hf hg
  | smul k f _ hf => rw [dilate_smul]; exact Submodule.smul_mem _ k hf

/-- **The idele-scaled Poisson formula (GZ5)**: `AdelicPoissonScaled`. -/
theorem adelicPoissonScaled : AdelicPoissonScaled := by
  intro f hf a
  obtain ⟨h1, h2, h3⟩ := adelicPoissonSummation (dilate a f) (dilate_mem a hf)
  have hF : ∀ q : ℚ, adelicFourier (dilate a f) (principal q) =
      (((ideleNorm a)⁻¹ : ℝ) : ℂ) * adelicFourier f (ideleToAdele a⁻¹ * principal q) :=
    fun q => adelicFourier_dilate a f _
  simp only [hF] at h3
  rw [tsum_mul_left] at h3
  exact h3

end GlobalTate.Poisson
