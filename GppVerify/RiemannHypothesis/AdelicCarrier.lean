/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.Upstream.RatAdeleRingEquiv
import GppVerify.RiemannHypothesis.AdelicFundamentalDomain


/-!
# The concrete carrier is Mathlib's adele ring (GP0)

The global Tate build runs on the concrete carrier `AQ = ℝ × 𝔸_f` (Turbo's ruling, GPP-bridge
PR #11, 6730857794). GP0 is the obligation to identify it with Mathlib's `AdeleRing ℤ ℚ`. The
identification itself is Mathlib-only and lives in `Upstream/RatAdeleRingEquiv.lean`
(`Rat.AdeleRing.ringEquivProd`, `Rat.AdeleRing.homeomorphProd`). Here:

* `principal_eq_ringEquivProd_algebraMap`: the concrete diagonal `principal` is Mathlib's
  diagonal `algebraMap ℚ (AdeleRing ℤ ℚ)` carried across the equivalence;
* `discrete_range_algebraMap` (GP1) and `compactSpace_adele_quotient` (GP2): discreteness and
  cocompactness of `ℚ` in Mathlib's `AdeleRing ℤ ℚ`, carried over from the concrete carrier.

Sequencing (GP-DUAL, then the Poisson file, then GP0): Turbo, GPP-bridge PR #11,
6732493269 and 6732913698.
-/

open IsDedekindDomain

namespace GlobalTate.Poisson

/-- Mathlib's diagonal, carried across `𝔸_ℚ ≃ ℝ × 𝔸_ℚ^f`, is the concrete `principal`. -/
theorem principal_eq_ringEquivProd_algebraMap (q : ℚ) :
    principal q = Rat.AdeleRing.ringEquivProd (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ) q) := by
  rw [Rat.AdeleRing.ringEquivProd_algebraMap]
  rfl

/-- Mathlib's diagonal image of `ℚ`, carried to the concrete carrier, is the principal adeles. -/
theorem image_range_algebraMap :
    Rat.AdeleRing.homeomorphProd '' Set.range (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)) =
      Set.range principal := by
  ext x
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, (principal_eq_ringEquivProd_algebraMap q).trans
      (Rat.AdeleRing.homeomorphProd_apply _).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨q, rfl⟩, (Rat.AdeleRing.homeomorphProd_apply _).trans
      (principal_eq_ringEquivProd_algebraMap q).symm⟩

/-- **GP1 for Mathlib's carrier.** `ℚ` is discrete in `AdeleRing ℤ ℚ`. -/
theorem discrete_range_algebraMap :
    DiscreteTopology (Set.range (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ))) := by
  have h : DiscreteTopology ((Rat.AdeleRing.homeomorphProd '' Set.range
      (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ))) : Set AQ) := by
    rw [image_range_algebraMap]
    exact principal_discrete
  exact (Rat.AdeleRing.homeomorphProd.image _).discreteTopology_iff.2 h

/-- **GP2 for Mathlib's carrier.** `AdeleRing ℤ ℚ ⧸ ℚ` is compact. -/
theorem compactSpace_adele_quotient :
    CompactSpace (NumberField.AdeleRing ℤ ℚ ⧸
      (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)).range.toAddSubgroup) := by
  have hK : IsCompact (Rat.AdeleRing.homeomorphProd.symm ''
      (Set.Icc (0 : ℝ) 1 ×ˢ intBox)) :=
    (isCompact_Icc.prod isCompact_intBox).image Rat.AdeleRing.homeomorphProd.symm.continuous
  refine ⟨?_⟩
  have : (Set.univ : Set (NumberField.AdeleRing ℤ ℚ ⧸
      (algebraMap ℚ (NumberField.AdeleRing ℤ ℚ)).range.toAddSubgroup)) =
      QuotientAddGroup.mk '' (Rat.AdeleRing.homeomorphProd.symm ''
        (Set.Icc (0 : ℝ) 1 ×ˢ intBox)) := by
    refine (Set.eq_univ_of_forall fun c => ?_).symm
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨q, hq, -⟩ := existsUnique_sub_principal_mem_fundBox (Rat.AdeleRing.homeomorphProd x)
      have hz : Rat.AdeleRing.homeomorphProd (x - algebraMap ℚ _ q) =
          Rat.AdeleRing.homeomorphProd x - principal q := by
        rw [Rat.AdeleRing.homeomorphProd_apply, Rat.AdeleRing.homeomorphProd_apply, map_sub,
          principal_eq_ringEquivProd_algebraMap q]
      refine ⟨x - algebraMap ℚ _ q, ⟨_, ?_, Homeomorph.symm_apply_apply _ _⟩, ?_⟩
      · rw [hz]
        exact ⟨Set.Ico_subset_Icc_self hq.1, hq.2⟩
      · rw [QuotientAddGroup.eq]
        simp only [neg_sub]
        exact ⟨q, by simp⟩
  rw [this]
  exact hK.image QuotientAddGroup.continuous_mk

end GlobalTate.Poisson
