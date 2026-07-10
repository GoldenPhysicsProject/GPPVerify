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
(as fibers of the quotient map, a generic fact about `Quotient`/`Setoid`), and each coset
has the same measure as `H` (left-invariance).
-/

namespace GppHaarSubgroupIndex

open MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- Translating a set by a group element preserves its measure under a left-invariant
    measure `μ`. -/
theorem measure_smul_set (μ : Measure G) [μ.IsMulLeftInvariant] (g : G) (s : Set G) :
    μ (g • s) = μ s := by
  have heq : g • s = (fun h => g⁻¹ * h) ⁻¹' s := by
    ext x
    simp only [Set.mem_smul_set, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨g⁻¹ * x, hx, by group⟩
  rw [heq, measure_preimage_mul]

/-- Distinct left cosets `x.out • H` (for `x : G ⧸ H`) are pairwise disjoint: each coset
    is exactly the fiber of the quotient map `QuotientGroup.mk` over `x`, and fibers of
    a function over distinct points are always disjoint. -/
theorem cosets_pairwise_disjoint (H : Subgroup G) :
    Pairwise (Function.onFun Disjoint (fun x : G ⧸ H => x.out • (H : Set G))) := by
  have hfiber : ∀ x : G ⧸ H, x.out • (H : Set G) = (QuotientGroup.mk (s := H)) ⁻¹' {x} := by
    intro x
    ext g
    simp only [Set.mem_smul_set, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h, hh, rfl⟩
      have : (QuotientGroup.mk (x.out * h) : G ⧸ H) = QuotientGroup.mk x.out := by
        rw [QuotientGroup.eq]
        simpa using (H.inv_mem hh)
      rw [this, QuotientGroup.out_eq']
    · intro hg
      have hrel : (x.out)⁻¹ * g ∈ H := by
        have : (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk x.out := by
          rw [hg, QuotientGroup.out_eq']
        rwa [QuotientGroup.eq, eq_comm] at this
      exact ⟨(x.out)⁻¹ * g, hrel, by group⟩
  intro x y hxy
  simp only [Function.onFun]
  rw [hfiber x, hfiber y]
  exact Set.disjoint_left.mpr (by
    intro a hax hay
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hax hay
    exact hxy (hax ▸ hay ▸ rfl))

/-- **Haar measure of a finite-index measurable subgroup**: `H.index • μ H = μ univ`. -/
theorem index_smul_measure_eq_univ (μ : Measure G) [μ.IsMulLeftInvariant]
    (H : Subgroup G) [Finite (G ⧸ H)] (hHmeas : MeasurableSet (H : Set G)) :
    (Nat.card (G ⧸ H)) • μ H = μ Set.univ := by
  classical
  have hunion : (Set.univ : Set G) = ⋃ x : G ⧸ H, x.out • (H : Set G) :=
    QuotientGroup.univ_eq_iUnion_smul H
  have hmeas : ∀ x : G ⧸ H, MeasurableSet (x.out • (H : Set G)) := fun x =>
    hHmeas.const_smul (x.out)
  rw [hunion, measure_iUnion (cosets_pairwise_disjoint H) hmeas]
  have hconst : ∀ x : G ⧸ H, μ (x.out • (H : Set G)) = μ (H : Set G) := fun x =>
    measure_smul_set μ x.out (H : Set G)
  simp only [hconst]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

end GppHaarSubgroupIndex
