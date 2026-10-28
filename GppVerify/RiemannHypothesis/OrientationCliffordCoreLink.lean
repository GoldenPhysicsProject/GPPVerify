import GppVerify.StandardModel.OrientationCliffordCore
import GppVerify.StandardModel.FourOrientationGaugeProjection
import GppVerify.StandardModel.OrientationComplexStructureDoubleCover
import GppVerify.RiemannHypothesis.OrientationCriticalRealStructureBridge
import GppVerify.RiemannHypothesis.HolographicReflectionPositivity

/-!
# Linking the Clifford core to the RH-side orientation files

`OrientationCliffordCore.lean` (StandardModel) and the RH-side orientation
files — `FourOrientationGaugeProjection.lean`,
`OrientationComplexStructureDoubleCover.lean` and
`OrientationCriticalRealStructureBridge.lean` — formalize the same
four-lift orientation algebra in two different carriers:

* the core: explicit `4 × 4` matrices over the Gaussian integers `ℤ[i]`
  acting on `Fin 4 → ℤ[i]`;
* the RH side: coordinate functions on `Orientation4 = ℂ × ℂ × ℂ × ℂ`.

Before this file, no module imported both sides. This file links them by
the canonical embedding `GaussianInt.toComplex : ℤ[i] →+* ℂ`:

* **The operator dictionary** (`embedVec_D`, `embedVec_Rq`, `embedVec_Rt`,
  `embedVec_chiL`, `embedVec_Iq`, `embedVec_It`): the embedding
  intertwines every operator that is named on both sides — `D` with
  `diagReverse`, `Rq` with `chargeFlip`, `Rt` with `temporalFlip`,
  `χ_L` with `chi`, and the two complex structures `Iq`, `It`.
* **The real forms coincide** (`fixD_iff_diagReverse_embed`,
  `embedVec_fixD`): a Gaussian vector is `D`-fixed iff its image is
  `diagReverse`-fixed, and `D`-fixed vectors embed exactly onto the
  bridge's physical lifts `physicalLift a b = (a, b, b, a)`.
* **The scalar shadow of the half-flip theorem**
  (`halfFlips_on_fixD_embed`, `chiL_on_fixD_embed`): transported through
  the embedding, the core's theorem that the two half flips coincide on
  `Fix(D)` says that on lift coordinates both flips act as the single
  swap `(a, b) ↦ (b, a)`, while `χ_L` acts as the bridge's
  `(a, b) ↦ (a, -b)` (`chi_on_physicalLift`). This is the finite content
  behind the bridge file's remark that its scalar correspondence
  `centered_shadow_eq_conj_iff_critical_real_form` is "the scalar
  arithmetic analogue of the v21 finite theorem that the two half flips
  coincide on the D-fixed real form".
* **The half flip against reflection positivity**
  (`Rt_action_via_rtPerm`, `rt_reflection_not_positive`): read as a
  permutation of the four labels, `Rt` is `(0 1)(2 3)`; instantiating
  `HolographicReflectionPositivity`'s `reflectionForm_nonneg_iff` at
  this permutation, its reflection form is not nonnegative — a half
  flip moves every label, so it has mirror pairs; in this finite
  picture positivity lives on the `D`-fixed real form.

Scope: the embedding hits only the Gaussian-integer points of
`Orientation4`; the statements are the `ℤ[i]`-form correspondence of
the named operators, not a complex-linear identification of the two
carriers. The tuple model's sign observables `bareQ`, `bareT` have no
named Clifford-core counterparts (on the core side they would be the
unnamed scalar multiples `(-i) • Iq`, `(-i) • It`), so they are not
part of the dictionary.
-/

open GppFourOrientationGaugeProjection
open Matrix

namespace GppOrientationCliffordCoreLink

open GppOrientationCliffordCore

/-- The vector embedding: a Gaussian-integer 4-vector as a complex
    orientation tuple, via `GaussianInt.toComplex`. -/
def embedVec (v : Fin 4 → GaussianInt) : Orientation4 :=
  ((v 0 : ℂ), (v 1 : ℂ), (v 2 : ℂ), (v 3 : ℂ))

theorem embedVec_injective : Function.Injective embedVec := by
  intro v w h
  have h0 : (v 0 : ℂ) = (w 0 : ℂ) := congrArg Prod.fst h
  have h1 : (v 1 : ℂ) = (w 1 : ℂ) := congrArg (fun x : Orientation4 => x.2.1) h
  have h2 : (v 2 : ℂ) = (w 2 : ℂ) := congrArg (fun x : Orientation4 => x.2.2.1) h
  have h3 : (v 3 : ℂ) = (w 3 : ℂ) := congrArg (fun x : Orientation4 => x.2.2.2) h
  funext i
  fin_cases i
  · exact GaussianInt.toComplex_injective h0
  · exact GaussianInt.toComplex_injective h1
  · exact GaussianInt.toComplex_injective h2
  · exact GaussianInt.toComplex_injective h3

/-- The core's `χ_L` is the diagonal grading `diag(1, -1, -1, 1)`. -/
theorem chiL_eq_diag : chiL
    = !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] := by
  decide

theorem embedVec_D (v : Fin 4 → GaussianInt) :
    embedVec (D *ᵥ v) = diagReverse (embedVec v) := by
  have h0 : (D *ᵥ v) 0 = v 3 := by
    simp [D, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h1 : (D *ᵥ v) 1 = v 2 := by
    simp [D, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h2 : (D *ᵥ v) 2 = v 1 := by
    simp [D, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h3 : (D *ᵥ v) 3 = v 0 := by
    simp [D, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  simp only [embedVec, diagReverse, h0, h1, h2, h3]

theorem embedVec_Rq (v : Fin 4 → GaussianInt) :
    embedVec (Rq *ᵥ v) = chargeFlip (embedVec v) := by
  have h0 : (Rq *ᵥ v) 0 = v 2 := by
    simp [Rq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h1 : (Rq *ᵥ v) 1 = v 3 := by
    simp [Rq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h2 : (Rq *ᵥ v) 2 = v 0 := by
    simp [Rq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h3 : (Rq *ᵥ v) 3 = v 1 := by
    simp [Rq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  simp only [embedVec, chargeFlip, h0, h1, h2, h3]

theorem embedVec_Rt (v : Fin 4 → GaussianInt) :
    embedVec (Rt *ᵥ v) = temporalFlip (embedVec v) := by
  have h0 : (Rt *ᵥ v) 0 = v 1 := by
    simp [Rt, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h1 : (Rt *ᵥ v) 1 = v 0 := by
    simp [Rt, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h2 : (Rt *ᵥ v) 2 = v 3 := by
    simp [Rt, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h3 : (Rt *ᵥ v) 3 = v 2 := by
    simp [Rt, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  simp only [embedVec, temporalFlip, h0, h1, h2, h3]

theorem embedVec_chiL (v : Fin 4 → GaussianInt) :
    embedVec (chiL *ᵥ v) = GppFourOrientationGaugeProjection.chi (embedVec v) := by
  have h0 : (chiL *ᵥ v) 0 = v 0 := by
    simp [chiL_eq_diag, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct,
      Fin.sum_univ_four]
  have h1 : (chiL *ᵥ v) 1 = - v 1 := by
    simp [chiL_eq_diag, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct,
      Fin.sum_univ_four]
  have h2 : (chiL *ᵥ v) 2 = - v 2 := by
    simp [chiL_eq_diag, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct,
      Fin.sum_univ_four]
  have h3 : (chiL *ᵥ v) 3 = v 3 := by
    simp [chiL_eq_diag, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct,
      Fin.sum_univ_four]
  simp only [embedVec, GppFourOrientationGaugeProjection.chi, h0, h1, h2, h3,
    GaussianInt.toComplex_neg]

theorem embedVec_Iq (v : Fin 4 → GaussianInt) :
    embedVec (Iq *ᵥ v)
      = GppOrientationComplexStructureDoubleCover.Iq (embedVec v) := by
  have h0 : (Iq *ᵥ v) 0 = ii * v 0 := by
    simp [Iq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h1 : (Iq *ᵥ v) 1 = ii * v 1 := by
    simp [Iq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h2 : (Iq *ᵥ v) 2 = -ii * v 2 := by
    simp [Iq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h3 : (Iq *ᵥ v) 3 = -ii * v 3 := by
    simp [Iq, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have hii : ((ii : GaussianInt) : ℂ) = Complex.I := by
    simp [ii, GaussianInt.toComplex_def']
  simp only [embedVec, GppOrientationComplexStructureDoubleCover.Iq, h0, h1, h2,
    h3, GaussianInt.toComplex_mul, GaussianInt.toComplex_neg, hii]

theorem embedVec_It (v : Fin 4 → GaussianInt) :
    embedVec (It *ᵥ v)
      = GppOrientationComplexStructureDoubleCover.It (embedVec v) := by
  have h0 : (It *ᵥ v) 0 = ii * v 0 := by
    simp [It, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h1 : (It *ᵥ v) 1 = -ii * v 1 := by
    simp [It, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h2 : (It *ᵥ v) 2 = ii * v 2 := by
    simp [It, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have h3 : (It *ᵥ v) 3 = -ii * v 3 := by
    simp [It, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct, Fin.sum_univ_four]
  have hii : ((ii : GaussianInt) : ℂ) = Complex.I := by
    simp [ii, GaussianInt.toComplex_def']
  simp only [embedVec, GppOrientationComplexStructureDoubleCover.It, h0, h1, h2,
    h3, GaussianInt.toComplex_mul, GaussianInt.toComplex_neg, hii]

/-- The two real forms coincide under the embedding: a Gaussian vector is
    `D`-fixed iff its complex image is `diagReverse`-fixed. -/
theorem fixD_iff_diagReverse_embed (v : Fin 4 → GaussianInt) :
    diagReverse (embedVec v) = embedVec v ↔ D *ᵥ v = v := by
  rw [← embedVec_D]
  constructor
  · intro h
    exact embedVec_injective h
  · intro h
    rw [h]

/-- `D`-fixed Gaussian vectors embed exactly onto physical lifts, with the
    two scalar coordinates read off the vector. -/
theorem embedVec_fixD (v : Fin 4 → GaussianInt) (hv : D *ᵥ v = v) :
    embedVec v = physicalLift ((v 0 : ℂ)) ((v 1 : ℂ)) := by
  obtain ⟨h03, h12⟩ := (fixD_iff v).mp hv
  have e2 : v 2 = v 1 := h12.symm
  have e3 : v 3 = v 0 := h03.symm
  simp only [embedVec, physicalLift, e2, e3]

/-- **The half flips on the real form, transported.** For a `D`-fixed
    Gaussian vector, both Clifford-core half flips embed to the *same*
    physical lift with the two scalar coordinates swapped: the common
    scalar action of `Rq` and `Rt` on `Fix(D)` is the swap
    `(a, b) ↦ (b, a)` of the lift coordinates. This is the transported
    content of `halfFlips_agree_on_fixD`. -/
theorem halfFlips_on_fixD_embed (v : Fin 4 → GaussianInt) (hv : D *ᵥ v = v) :
    embedVec (Rq *ᵥ v) = physicalLift ((v 1 : ℂ)) ((v 0 : ℂ)) ∧
    embedVec (Rt *ᵥ v) = physicalLift ((v 1 : ℂ)) ((v 0 : ℂ)) := by
  constructor
  · rw [embedVec_Rq, embedVec_fixD v hv]
    rfl
  · rw [embedVec_Rt, embedVec_fixD v hv]
    rfl

/-- **The relative grading on the real form, transported.** For a
    `D`-fixed Gaussian vector, the core's `χ_L` embeds to the bridge's
    scalar action `(a, b) ↦ (a, -b)` on the lift coordinates — the
    `chi_on_physicalLift` of the critical-real-structure bridge. -/
theorem chiL_on_fixD_embed (v : Fin 4 → GaussianInt) (hv : D *ᵥ v = v) :
    embedVec (chiL *ᵥ v)
      = physicalLift ((v 0 : ℂ)) (-((v 1 : ℂ))) := by
  rw [embedVec_chiL, embedVec_fixD v hv]
  exact GppOrientationCriticalRealStructureBridge.chi_on_physicalLift _ _

/-- The label permutation induced by `Rt`'s coordinate action:
    `(Rt *ᵥ v) i = v (rtPerm i)`. -/
def rtPerm : Fin 4 → Fin 4 := ![1, 0, 3, 2]

theorem Rt_action_via_rtPerm (v : Fin 4 → GaussianInt) (i : Fin 4) :
    (Rt *ᵥ v) i = v (rtPerm i) := by
  fin_cases i <;>
    simp [rtPerm, Rt, Matrix.cons_mulVec, Matrix.empty_mulVec, dotProduct,
      Fin.sum_univ_four]

/-- **The half flip's label reflection is not reflection-positive.**
    Instantiating `GppHolographicRP.reflectionForm_nonneg_iff` at the
    label permutation of `Rt` (with unit multiplicities): since `Rt`
    moves every label — its mirror pairs are `(0 1)` and `(2 3)` — the
    reflection form of the half flip is not nonnegative. Positivity in
    this finite picture lives on the `D`-fixed real form, not on the
    half-flip reflection of the labels. -/
theorem rt_reflection_not_positive :
    ¬ ∀ v : Fin 4 → ℂ,
      0 ≤ (GppHolographicRP.reflectionForm rtPerm (fun _ => 1) v).re := by
  intro h
  have hfix := (GppHolographicRP.reflectionForm_nonneg_iff rtPerm
    (by decide) (fun _ => 1) (fun _ => one_pos)).mp h
  exact absurd (hfix 0) (by decide)

end GppOrientationCliffordCoreLink
