/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance: Claude Code)
-/
import GppVerify.RiemannHypothesis.WeilFormHilbert

/-!
# The unitary dilation group of the arithmetic Hilbert space

On the Hilbert space `H` of `WeilFormHilbert` (the completion of test functions under the Weil
form), translation of the log variable `f ↦ f(· - t)` preserves the form (`weilBilFun_shift`), hence
extends by density to a unitary operator `U_t` of `H` with `U_t (ι f) = ι (shift t f)`, and
`t ↦ U_t` is a group: `U_0 = 1`, `U_{s+t} = U_s U_t` (`exists_dilation_group`).

The extension is by Mathlib's `LinearMap.extendOfNorm` along the dense map `ι`, and the group law
and `U_0 = 1` are `extendOfNorm_unique`. No zero of `ζ` enters. The hypothesis is arithmetic
reflection positivity, equivalent by `arp_iff_rh_strip` to every zero lying on `Re = 1/2`.
Continuity of `t ↦ U_t x` is a separate statement and is not part of this file.
-/

open MeasureTheory Set GppArithmeticReflection GppMeyerSpectralWeil GppWeilHilbert
open scoped ContDiff InnerProductSpace

noncomputable section

namespace GppWeilDilation

/-- Translation of the log variable, as a linear self-map of the test space. -/
def tshift (t : ℝ) : testSubmodule →ₗ[ℝ] testSubmodule where
  toFun f := ⟨GppZeroHilbert.shift t f.1, GppZeroHilbert.isTestFunction_shift t f.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[simp] theorem tshift_val (t : ℝ) (f : testSubmodule) :
    ((tshift t f : testSubmodule) : ℝ → ℝ) = GppZeroHilbert.shift t f.1 := rfl

theorem tshift_add (s t : ℝ) (f : testSubmodule) : tshift (s + t) f = tshift s (tshift t f) := by
  refine Subtype.ext (funext fun u => ?_)
  simp only [tshift_val, GppZeroHilbert.shift]
  congr 1; ring

theorem tshift_zero (f : testSubmodule) : tshift 0 f = f := by
  refine Subtype.ext (funext fun u => ?_)
  simp [GppZeroHilbert.shift]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : testSubmodule →ₗ[ℝ] H}

theorem inner_tshift (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (t : ℝ)
    (f g : testSubmodule) : ⟪ι (tshift t f), ι (tshift t g)⟫_ℝ = ⟪ι f, ι g⟫_ℝ := by
  rw [← hι, ← hι]
  exact weilBilFun_shift t f.1 g.1

theorem norm_tshift (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (t : ℝ)
    (f : testSubmodule) : ‖ι (tshift t f)‖ = ‖ι f‖ := by
  have h := inner_tshift hι t f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The extension of translation by `t` to `H`. -/
def Uop (_hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (t : ℝ) : H →L[ℝ] H :=
  (ι ∘ₗ tshift t).extendOfNorm ι

theorem Uop_bound (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (t : ℝ) :
    ∀ f, ‖(ι ∘ₗ tshift t) f‖ ≤ 1 * ‖ι f‖ := fun f => by
  simp only [LinearMap.comp_apply, one_mul]; exact (norm_tshift hι t f).le

theorem Uop_apply (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (t : ℝ) (f : testSubmodule) : Uop hι t (ι f) = ι (tshift t f) :=
  LinearMap.extendOfNorm_eq hd ⟨1, Uop_bound hι t⟩ f

theorem Uop_norm (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (t : ℝ) (x : H) : ‖Uop hι t x‖ = ‖x‖ := by
  refine hd.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) (fun f => ?_)
  rw [Uop_apply hι hd, norm_tshift hι]

theorem Uop_zero (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (x : H) : Uop hι 0 x = x := by
  have := LinearMap.extendOfNorm_unique (f := ι ∘ₗ tshift 0) (e := ι) hd 1 (Uop_bound hι 0)
    (ContinuousLinearMap.id ℝ H) (by
      ext f; simp [tshift_zero])
  have h2 : Uop hι 0 = ContinuousLinearMap.id ℝ H := this
  rw [h2]; rfl

theorem Uop_add (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ)
    (hd : DenseRange ι) (s t : ℝ) (x : H) : Uop hι (s + t) x = Uop hι s (Uop hι t x) := by
  have := LinearMap.extendOfNorm_unique (f := ι ∘ₗ tshift (s + t)) (e := ι) hd 1
    (Uop_bound hι (s + t)) ((Uop hι s).comp (Uop hι t)) (by
      ext f
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
        ContinuousLinearMap.coe_coe]
      rw [Uop_apply hι hd, Uop_apply hι hd, tshift_add])
  have h2 : Uop hι (s + t) = (Uop hι s).comp (Uop hι t) := this
  rw [h2]; rfl

/-- The unitary `U_t` of `H`. -/
def U (hι : ∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) (hd : DenseRange ι) (t : ℝ) :
    H ≃ₗᵢ[ℝ] H where
  toFun := Uop hι t
  invFun := Uop hι (-t)
  map_add' := (Uop hι t).map_add
  map_smul' := (Uop hι t).map_smul
  left_inv x := by rw [← Uop_add hι hd, neg_add_cancel, Uop_zero hι hd]
  right_inv x := by rw [← Uop_add hι hd, add_neg_cancel, Uop_zero hι hd]
  norm_map' := Uop_norm hι hd t

/-- **The arithmetic Hilbert space carries a unitary dilation group.** Given arithmetic reflection
positivity: a real Hilbert space `H`, a dense linear `ι` from test functions with Gram form the
Weil form, and unitaries `U t` with `U 0 = 1`, `U (s + t) = U s ∘ U t` and
`U t (ι f) = ι (f(· - t))`. -/
theorem exists_dilation_group (harp : ArithmeticReflectionPositivity) :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (ι : testSubmodule →ₗ[ℝ] K) (V : ℝ → (K ≃ₗᵢ[ℝ] K)),
      (∀ f g : testSubmodule, weilBilFun f.1 g.1 = ⟪ι f, ι g⟫_ℝ) ∧ DenseRange ι ∧
      (∀ x, V 0 x = x) ∧ (∀ s t x, V (s + t) x = V s (V t x)) ∧
      (∀ t f, V t (ι f) = ι (tshift t f)) := by
  obtain ⟨K, _, _, _, ι, hι, hd⟩ := exists_hilbert_weil harp
  exact ⟨K, inferInstance, inferInstance, inferInstance, ι, U hι hd, hι, hd,
    Uop_zero hι hd, Uop_add hι hd, fun t f => Uop_apply hι hd t f⟩

end GppWeilDilation

#print axioms GppWeilDilation.Uop_norm
#print axioms GppWeilDilation.Uop_add
#print axioms GppWeilDilation.exists_dilation_group
