/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.MeasureTheory.Measure.Haar.Basic


/-!
# Haar measure on the finite adeles of `ℚ`

We show that the finite adele ring `𝔸_{ℚ,f} = FiniteAdeleRing ℤ ℚ` is locally compact, that the
set `∏_v ℤ_v` of everywhere-integral finite adeles is compact and open, and we define the Haar
measure on `𝔸_{ℚ,f}` normalized so that `∏_v ℤ_v` has measure `1`.

## Main declarations

* `Rat.FiniteAdeleRing.isCompact_adicCompletionIntegers`: each `v.adicCompletionIntegers ℚ` is
  compact (it is homeomorphic to `ℤ_[p]` via `adicCompletion.padicEquiv`).
* `Rat.FiniteAdeleRing.integralAdeles`: the set `∏_v ℤ_v`, compact (`isCompact_integralAdeles`)
  and open (`isOpen_integralAdeles`).
* `Rat.FiniteAdeleRing.haar`: the Haar measure with `haar integralAdeles = 1`
  (`haar_integralAdeles`).

## Implementation notes

The measurable structure on `𝔸_{ℚ,f}` is the Borel σ-algebra. The file depends only on Mathlib
and is written to be upstreamed.
-/

open IsDedekindDomain Rat.HeightOneSpectrum MeasureTheory

namespace Rat.FiniteAdeleRing

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable (v : HeightOneSpectrum ℤ)

theorem mem_adicCompletionIntegers_iff (x : v.adicCompletion ℚ) :
    x ∈ v.adicCompletionIntegers ℚ ↔ ‖adicCompletion.padicEquiv v x‖ ≤ 1 := by
  have h := adicCompletion.padicEquiv_bijOn v
  constructor
  · intro hx; exact h.mapsTo hx
  · intro hx
    obtain ⟨y, hy, hyx⟩ := h.surjOn (show adicCompletion.padicEquiv v x ∈
      (PadicInt.subring (primesEquiv v) : Set _) from hx)
    rwa [(adicCompletion.padicEquiv v).injective hyx] at hy

/-- Every element of `ℚ_v` becomes integral after multiplication by a power of `p`. -/
theorem exists_pow_mul_mem_adicCompletionIntegers (x : v.adicCompletion ℚ) :
    ∃ k : ℕ, ((primesEquiv v : ℕ) : v.adicCompletion ℚ) ^ k * x ∈ v.adicCompletionIntegers ℚ := by
  set y := adicCompletion.padicEquiv v x
  have hp : (1 : ℝ) < (primesEquiv v : ℕ) := Nat.one_lt_cast.mpr (primesEquiv v).2.one_lt
  by_cases hy : y = 0
  · refine ⟨0, ?_⟩
    rw [mem_adicCompletionIntegers_iff, map_mul]
    rw [pow_zero, map_one, one_mul]
    change ‖y‖ ≤ 1
    rw [hy, norm_zero]
    exact zero_le_one
  refine ⟨(-y.valuation).toNat, ?_⟩
  rw [mem_adicCompletionIntegers_iff, map_mul, map_pow, map_natCast, norm_mul, norm_pow,
    Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hy, inv_pow, ← zpow_natCast, ← zpow_neg,
    ← zpow_add₀ (by positivity)]
  apply zpow_le_one_of_nonpos₀ hp.le
  have := Int.self_le_toNat (-y.valuation)
  omega

theorem isCompact_adicCompletionIntegers :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have e : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (adicCompletion.padicEquiv v) ⁻¹' Metric.closedBall 0 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_adicCompletionIntegers_iff, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right]
  rw [e]
  exact (adicCompletion.padicEquiv v).toHomeomorph.isCompact_preimage.2 (isCompact_closedBall _ _)

instance : LocallyCompactSpace (v.adicCompletion ℚ) :=
  (adicCompletion.padicEquiv v).toHomeomorph.isOpenEmbedding.locallyCompactSpace

instance : CompactSpace (v.adicCompletionIntegers ℚ) :=
  isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers v)

instance : Fact (∀ w : HeightOneSpectrum ℤ,
    IsOpen (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ))) :=
  ⟨fun _ => Valued.isOpen_integer _⟩

instance : T2Space (FiniteAdeleRing ℤ ℚ) :=
  inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Filter.cofinite))

instance : WeaklyLocallyCompactSpace (FiniteAdeleRing ℤ ℚ) :=
  inferInstanceAs (WeaklyLocallyCompactSpace (RestrictedProduct
    (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
    (fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    Filter.cofinite))

instance : LocallyCompactSpace (FiniteAdeleRing ℤ ℚ) := inferInstance

/-- The finite adeles that are integral at every place, `∏_v ℤ_v`. -/
def integralAdeles : Set (FiniteAdeleRing ℤ ℚ) := {f | ∀ v, f v ∈ v.adicCompletionIntegers ℚ}

theorem isOpen_integralAdeles : IsOpen integralAdeles :=
  RestrictedProduct.isOpen_forall_mem fun _ => Valued.isOpen_integer _

theorem isCompact_integralAdeles : IsCompact integralAdeles := by
  let incl : ((v : HeightOneSpectrum ℤ) → v.adicCompletionIntegers ℚ) → FiniteAdeleRing ℤ ℚ :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      Filter.cofinite
  have hc : Continuous incl :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (A := fun v : HeightOneSpectrum ℤ => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      (𝓕 := Filter.cofinite)).continuous
  have heq : integralAdeles = incl '' Set.univ := by
    ext a
    simp only [integralAdeles, Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    constructor
    · intro ha; exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v; exact (x v).2
  rw [heq]
  exact isCompact_univ.image hc

theorem zero_mem_integralAdeles : (0 : FiniteAdeleRing ℤ ℚ) ∈ integralAdeles :=
  fun v => (v.adicCompletionIntegers ℚ).zero_mem

open Classical in
/-- Every finite adele has bounded denominators: some positive integer multiple is integral. -/
theorem exists_nat_mul_mem_integralAdeles (f : FiniteAdeleRing ℤ ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ v, (N : v.adicCompletion ℚ) * f v ∈ v.adicCompletionIntegers ℚ := by
  have hS : {v : HeightOneSpectrum ℤ | f v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.1 f.2
  choose k hk using fun v => exists_pow_mul_mem_adicCompletionIntegers v (f v)
  refine ⟨∏ v ∈ hS.toFinset, (primesEquiv v : ℕ) ^ k v,
    Finset.prod_pos fun v _ => pow_pos (primesEquiv v).2.pos _, fun w => ?_⟩
  have hnat : ∀ n : ℕ, (n : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ :=
    fun n => natCast_mem (w.adicCompletionIntegers ℚ) n
  by_cases hw : w ∈ hS.toFinset
  · rw [← Finset.mul_prod_erase _ _ hw, Nat.cast_mul, Nat.cast_pow, mul_right_comm]
    exact mul_mem (hk w) (hnat _)
  · have hfw : f w ∈ w.adicCompletionIntegers ℚ := by
      simpa using hw
    exact mul_mem (hnat _) hfw

instance : SigmaCompactSpace (FiniteAdeleRing ℤ ℚ) := by
  refine ⟨⟨fun n => (fun f => algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((n : ℚ) + 1)⁻¹ * f) ''
    integralAdeles, fun n => isCompact_integralAdeles.image (continuous_const.mul continuous_id),
    Set.eq_univ_of_forall fun f => ?_⟩⟩
  obtain ⟨N, hN, hNf⟩ := exists_nat_mul_mem_integralAdeles f
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hN
  refine Set.mem_iUnion.2 ⟨n, (algebraMap ℚ _ ((n : ℚ) + 1)) * f, fun v => ?_, ?_⟩
  · show (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((n : ℚ) + 1) * f) v ∈ _
    rw [show (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((n : ℚ) + 1) * f) v =
      algebraMap ℚ (v.adicCompletion ℚ) ((n : ℚ) + 1) * f v from rfl,
      map_add, map_natCast, map_one]
    have := hNf v
    push_cast at this
    simpa using this
  · dsimp only
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by positivity), map_one, one_mul]

noncomputable instance : MeasurableSpace (FiniteAdeleRing ℤ ℚ) := borel _
instance : BorelSpace (FiniteAdeleRing ℤ ℚ) := ⟨rfl⟩

/-- `∏_v ℤ_v` as a compact set with nonempty interior. -/
noncomputable def integralAdelesPositiveCompacts : TopologicalSpace.PositiveCompacts (FiniteAdeleRing ℤ ℚ) where
  carrier := integralAdeles
  isCompact' := isCompact_integralAdeles
  interior_nonempty' := ⟨0, isOpen_integralAdeles.interior_eq.symm ▸ zero_mem_integralAdeles⟩

/-- The Haar measure on `𝔸_{ℚ,f}` normalized by `vol(∏_v ℤ_v) = 1`. -/
noncomputable def haar : Measure (FiniteAdeleRing ℤ ℚ) :=
  Measure.addHaarMeasure integralAdelesPositiveCompacts

instance : haar.IsAddHaarMeasure := by unfold haar; infer_instance

theorem haar_integralAdeles : haar integralAdeles = 1 :=
  Measure.addHaarMeasure_self

end Rat.FiniteAdeleRing
