import GppVerify.RiemannHypothesis.WeilPositivityCriterion
import Mathlib.Tactic

/-!
# Finite interpolation bridge to the Weil paired-form criterion

The finite Weil form on a set `S` only samples a coefficient function at points of
`S` and their involutive partners.  Consequently one does not need global
surjectivity of an explicit-formula transform onto all functions on the zero set.
It is enough that the test-transform class interpolate arbitrary data on each
finite set `S ∪ iota(S)`.

This file formalizes that exact reduction.  It deliberately does not assert that
any particular Schwartz/Mellin/Paley--Wiener test class has the required finite
interpolation property; proving that analytic statement is the genuine remaining
bridge.
-/

namespace GppWeilInterpolationBridge

open Finset
open GppWeilCriterion

/-- The exact finite support sampled by the paired form: `S` together with its
involutive partners.  This is noncomputable only because equality on `ℂ` is used to
form a `Finset`; the mathematical support itself is finite and explicit. -/
noncomputable def pairSupport (ι : ℂ → ℂ) (S : Finset ℂ) : Finset ℂ :=
  S ∪ S.image ι

/-- Every original point lies in the pair-support. -/
theorem mem_pairSupport_self {ι : ℂ → ℂ} {S : Finset ℂ} {ρ : ℂ}
    (hρ : ρ ∈ S) : ρ ∈ pairSupport ι S := by
  classical
  exact Finset.mem_union_left _ hρ

/-- Every involutive partner of a point of `S` lies in the pair-support. -/
theorem mem_pairSupport_image {ι : ℂ → ℂ} {S : Finset ℂ} {ρ : ℂ}
    (hρ : ρ ∈ S) : ι ρ ∈ pairSupport ι S := by
  classical
  unfold pairSupport
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩

/-- Agreement on `S` and `iota(S)` is enough to preserve the paired form on `S`. -/
theorem pairedForm_eq_of_agree_on_pairSupport
    {ι : ℂ → ℂ} {S : Finset ℂ} {c d : ℂ → ℂ}
    (hS : ∀ ρ ∈ S, d ρ = c ρ)
    (hiS : ∀ ρ ∈ S, d (ι ρ) = c (ι ρ)) :
    pairedForm ι S d = pairedForm ι S c := by
  unfold pairedForm
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [hS ρ hρ, hiS ρ hρ]

/-- Single-support form of the same fact: equality on `pairSupport iota S` is
exactly the finite information needed to preserve the paired form. -/
theorem pairedForm_eq_of_agree_on_pairSupport_union
    {ι : ℂ → ℂ} {S : Finset ℂ} {c d : ℂ → ℂ}
    (h : ∀ z ∈ pairSupport ι S, d z = c z) :
    pairedForm ι S d = pairedForm ι S c := by
  apply pairedForm_eq_of_agree_on_pairSupport
  · intro ρ hρ
    exact h ρ (mem_pairSupport_self hρ)
  · intro ρ hρ
    exact h (ι ρ) (mem_pairSupport_image hρ)

/-- Abstract finite interpolation principle: positivity for all coefficient functions
coming from a test-transform class implies positivity of the full finite paired form,
provided those transforms can interpolate arbitrary coefficient data on every finite
pair-support. -/
theorem pairedForm_nonneg_of_finite_interpolation
    {T : Type*} {ι : ℂ → ℂ} {Z : Set ℂ}
    (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ f : T,
      0 ≤ (pairedForm ι S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      ∃ f : T,
        (∀ ρ ∈ S, coeff f ρ = c ρ) ∧
        (∀ ρ ∈ S, coeff f (ι ρ) = c (ι ρ))) :
    ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm ι S c).re := by
  intro S hSZ c
  obtain ⟨f, hS, hiS⟩ := hinterp S hSZ c
  have heq : pairedForm ι S (coeff f) = pairedForm ι S c :=
    pairedForm_eq_of_agree_on_pairSupport hS hiS
  rw [← heq]
  exact htestPos S hSZ f

/-- Cleaner support-packaged interpolation principle.  No values away from the
finite set `pairSupport iota S` are relevant. -/
theorem pairedForm_nonneg_of_pairSupport_interpolation
    {T : Type*} {ι : ℂ → ℂ} {Z : Set ℂ}
    (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ f : T,
      0 ≤ (pairedForm ι S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      ∃ f : T, ∀ z ∈ pairSupport ι S, coeff f z = c z) :
    ∀ S : Finset ℂ, ↑S ⊆ Z → ∀ c : ℂ → ℂ,
      0 ≤ (pairedForm ι S c).re := by
  intro S hSZ c
  obtain ⟨f, hf⟩ := hinterp S hSZ c
  have heq : pairedForm ι S (coeff f) = pairedForm ι S c :=
    pairedForm_eq_of_agree_on_pairSupport_union hf
  rw [← heq]
  exact htestPos S hSZ f

/-- **Explicit interpolation-to-RH reduction.** If a test-transform class is positive
for the zeta paired form and has finite interpolation on every finite subset of the
nontrivial zero set together with its shadow partners, then RH follows by the already
proved finite Weil criterion.

This theorem is a reduction, not an RH proof: the two analytic hypotheses below are
exactly what an explicit-formula/Wiener--Hopf construction must discharge. -/
theorem rh_of_testPos_finiteInterpolation
    {T : Type*} (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ f : T,
      0 ≤ (pairedForm zetaInvolution S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
      ∃ f : T,
        (∀ ρ ∈ S, coeff f ρ = c ρ) ∧
        (∀ ρ ∈ S, coeff f (zetaInvolution ρ) = c (zetaInvolution ρ))) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_iff_weil_pairedForm_nonneg.mpr
  exact pairedForm_nonneg_of_finite_interpolation coeff htestPos hinterp

/-- Pair-support packaged version of the interpolation-to-RH reduction.  This is the
minimal finite-surjectivity target for any proposed Mellin/Paley--Wiener realization:
only arbitrary values on `S ∪ zetaInvolution(S)` are required. -/
theorem rh_of_testPos_pairSupportInterpolation
    {T : Type*} (coeff : T → ℂ → ℂ)
    (htestPos : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ f : T,
      0 ≤ (pairedForm zetaInvolution S (coeff f)).re)
    (hinterp : ∀ S : Finset ℂ, ↑S ⊆ nontrivialZeros → ∀ c : ℂ → ℂ,
      ∃ f : T, ∀ z ∈ pairSupport zetaInvolution S, coeff f z = c z) :
    ∀ ρ ∈ nontrivialZeros, ρ.re = 1 / 2 := by
  apply rh_iff_weil_pairedForm_nonneg.mpr
  exact pairedForm_nonneg_of_pairSupport_interpolation coeff htestPos hinterp

end GppWeilInterpolationBridge

#print axioms GppWeilInterpolationBridge.pairedForm_eq_of_agree_on_pairSupport
#print axioms GppWeilInterpolationBridge.pairedForm_eq_of_agree_on_pairSupport_union
#print axioms GppWeilInterpolationBridge.pairedForm_nonneg_of_finite_interpolation
#print axioms GppWeilInterpolationBridge.pairedForm_nonneg_of_pairSupport_interpolation
#print axioms GppWeilInterpolationBridge.rh_of_testPos_finiteInterpolation
#print axioms GppWeilInterpolationBridge.rh_of_testPos_pairSupportInterpolation
