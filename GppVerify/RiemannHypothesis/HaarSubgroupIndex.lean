import Mathlib.MeasureTheory.Group.Measure
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index

/-!
# Haar measure of a finite-index measurable subgroup

Real infrastructure toward the p-adic/adelic integral computations underlying Tate's
thesis (needed to eventually compute `μ(pⁿ ℤ_p)` from the index of `pⁿ ℤ_p` in `ℤ_p`,
feeding the local zeta integral machinery `AdelicL2.lean`/`L2Constraint.lean` axiomatize).
Not sourced from a specific Golden Physics Project paper.

The classical fact: for a left-invariant measure `μ` on a group `G` and a measurable
subgroup `H` of finite index, `H.index • μ H = μ Set.univ` — i.e. `μ H = μ Set.univ /
H.index`. Proved from first principles: `G` is the disjoint union of the `H.index`-many
left cosets of `H` (`QuotientGroup.univ_eq_iUnion_smul`), distinct cosets are disjoint
(as fibers of the quotient map, via `QuotientGroup.eq_class_eq_leftCoset`), and each
coset has the same measure as `H` (left-invariance).
-/

namespace GppHaarSubgroupIndex

open MeasureTheory
open scoped Pointwise

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- A left translate of a set is the preimage of that set under (left) multiplication
    by the inverse element. -/
@[to_additive /-- A left translate of a set is the preimage of that set under (left)
    addition of the negation. -/]
theorem smul_eq_preimage_inv_mul (g : G) (s : Set G) :
    g • s = (fun h => g⁻¹ * h) ⁻¹' s := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_preimage, smul_eq_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [inv_mul_cancel_left]
  · intro hx
    exact ⟨g⁻¹ * x, hx, mul_inv_cancel_left g x⟩

/-- Translating a set by a group element preserves its measure under a left-invariant
    measure `μ`. -/
@[to_additive /-- Translating a set by a group element preserves its measure under a
    left-invariant measure `μ`. -/]
theorem measure_smul_set (μ : Measure G) [μ.IsMulLeftInvariant] (g : G) (s : Set G) :
    μ (g • s) = μ s := by
  rw [smul_eq_preimage_inv_mul, measure_preimage_mul]

/-- A left translate of a measurable set is measurable. -/
@[to_additive /-- A left translate of a measurable set is measurable. -/]
theorem measurableSet_smul {s : Set G} (hs : MeasurableSet s) (g : G) :
    MeasurableSet (g • s) := by
  rw [smul_eq_preimage_inv_mul]
  exact hs.preimage (measurable_const_mul g⁻¹)

/-- Distinct left cosets `x.out • H` (for `x : G ⧸ H`) are pairwise disjoint: each coset
    is exactly the fiber of the quotient map over `x`. -/
@[to_additive cosets_pairwise_disjoint_add /-- Distinct left cosets `x.out +ᵥ H` (for
    `x : G ⧸ H`) are pairwise disjoint: each coset is exactly the fiber of the quotient
    map over `x`. -/]
theorem cosets_pairwise_disjoint (H : Subgroup G) :
    Pairwise (Function.onFun Disjoint (fun x : G ⧸ H => x.out • (H : Set G))) := by
  have hfiber : ∀ x : G ⧸ H, x.out • (H : Set G) = {y : G | (y : G ⧸ H) = x} := by
    intro x
    have hxout : (x.out : G ⧸ H) = x := by simp
    rw [← QuotientGroup.eq_class_eq_leftCoset H x.out, hxout]
  intro x y hxy
  simp only [Function.onFun, hfiber]
  rw [Set.disjoint_left]
  intro a hax hay
  simp only [Set.mem_setOf_eq] at hax hay
  exact absurd (hax.symm.trans hay) hxy

/-- **Haar measure of a finite-index measurable subgroup**: `H.index • μ H = μ univ`. -/
theorem index_smul_measure_eq_univ (μ : Measure G) [μ.IsMulLeftInvariant]
    (H : Subgroup G) [Finite (G ⧸ H)] (hHmeas : MeasurableSet (H : Set G)) :
    (Nat.card (G ⧸ H)) • μ H = μ Set.univ := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hunion : (Set.univ : Set G) = ⋃ x : G ⧸ H, x.out • (H : Set G) :=
    QuotientGroup.univ_eq_iUnion_smul H
  have hmeas : ∀ x : G ⧸ H, MeasurableSet (x.out • (H : Set G)) := fun x =>
    measurableSet_smul hHmeas x.out
  rw [hunion, measure_iUnion (cosets_pairwise_disjoint H) hmeas]
  have hconst : ∀ x : G ⧸ H, μ (x.out • (H : Set G)) = μ (H : Set G) := fun x =>
    measure_smul_set μ x.out (H : Set G)
  simp only [hconst]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

/-- **Haar measure of a finite-index measurable subgroup, additive case**:
    `H.index • μ H = μ univ`. Written out by hand (rather than via `to_additive`, which
    hit a type-mismatch on this particular statement mixing group-translation `+ᵥ` with
    the unrelated `ℕ`-scalar action on `μ H : ℝ≥0∞`), reusing the additive helper lemmas
    `to_additive` *did* derive successfully above. -/
theorem index_vadd_measure_eq_univ {G : Type*} [AddGroup G] [MeasurableSpace G]
    [MeasurableAdd G] (μ : Measure G) [μ.IsAddLeftInvariant]
    (H : AddSubgroup G) [Finite (G ⧸ H)] (hHmeas : MeasurableSet (H : Set G)) :
    (Nat.card (G ⧸ H)) • μ H = μ Set.univ := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hunion : (Set.univ : Set G) = ⋃ x : G ⧸ H, x.out +ᵥ (H : Set G) :=
    QuotientAddGroup.univ_eq_iUnion_vadd H
  have hmeas : ∀ x : G ⧸ H, MeasurableSet (x.out +ᵥ (H : Set G)) := fun x =>
    measurableSet_vadd hHmeas x.out
  rw [hunion, measure_iUnion (cosets_pairwise_disjoint_add H) hmeas]
  have hconst : ∀ x : G ⧸ H, μ (x.out +ᵥ (H : Set G)) = μ (H : Set G) := fun x =>
    measure_vadd_set μ x.out (H : Set G)
  simp only [hconst]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

end GppHaarSubgroupIndex
