/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import Mathlib.NumberTheory.Padics.RingHoms
import GppVerify.RiemannHypothesis.AdelicDiscrete
import GppVerify.Upstream.RatFiniteAdeleRingApprox


/-!
# Strong approximation, the fundamental domain and cocompactness (GP3, GP2)

On the adele carrier `AQ = ℝ × 𝔸_f`:

* **Strong approximation for `ℚ`** (`exists_rat_sub_mem_integers`): every finite adele is a
  rational plus an adele integral at every place. Locally, every `x ∈ ℚ_p` is within `ℤ_p` of
  some `m / p^k`, which is integral at every other prime; the global statement follows by induction
  on the finitely many non-integral places. The proof is Mathlib-only and lives in
  `Upstream/RatFiniteAdeleRingApprox.lean`.
* **GP3** (`existsUnique_sub_principal_mem_fundBox`): every adele is uniquely a principal
  adele plus a point of the fundamental domain `[0, 1) × ∏ ℤ_v`.
* **GP2** (`principal_cocompact`): `AQ ⧸ ℚ` is compact, being the image of the compact set
  `[0, 1] × ∏ ℤ_v` (`isCompact_intBox`).

The covolume (GP4) needs a Haar measure on the adeles, normalized as Lebesgue at infinity times
`vol(∏ ℤ_p) = 1` (Turbo, GPP-bridge PR #11, 6730857794); that is the next piece.

Governing specification: Principal series's global Tate statement sheet (GPP-bridge branch
`principal-series/global-tate-statements` at `77d5b43`, §4), audited PASS by Turbo.
-/

namespace GlobalTate.Poisson

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Rat.HeightOneSpectrum GppIdeleQ

theorem padicEquiv_algebraMap (v : HeightOneSpectrum ℤ) (q : ℚ) :
    adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) q) = (q : ℚ_[pr v]) := by
  simp only [eq_ratCast, map_ratCast]

/-- A rational is integral at `v` iff its `pr v`-adic norm is at most one. -/
theorem algebraMap_mem_integers_iff (v : HeightOneSpectrum ℤ) (q : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ ↔ padicNorm (pr v) q ≤ 1 := by
  rw [mem_integers_iff, lnorm_algebraMap, Padic.eq_padicNorm]
  exact_mod_cast Iff.rfl

/-- **Strong approximation for `ℚ`.** Every finite adele is a rational plus an adele that is
integral at every place. (The proof is Mathlib-only and lives in
`Upstream/RatFiniteAdeleRingApprox.lean`.) -/
theorem exists_rat_sub_mem_integers (f : Af) :
    ∃ q : ℚ, ∀ v, f v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ :=
  Rat.FiniteAdeleRing.exists_rat_sub_mem_integralAdeles f

theorem intCast_mem_integers (v : HeightOneSpectrum ℤ) (n : ℤ) :
    algebraMap ℚ (v.adicCompletion ℚ) n ∈ v.adicCompletionIntegers ℚ :=
  (algebraMap_mem_integers_iff v n).2 (padicNorm.of_int n)

/-- The fundamental domain `[0, 1) × ∏ ℤ_v`. -/
def fundBox : Set AQ := Set.Ico (0 : ℝ) 1 ×ˢ intBox

theorem algebraMap_Af_apply (q : ℚ) (v : HeightOneSpectrum ℤ) :
    algebraMap ℚ Af q v = algebraMap ℚ (v.adicCompletion ℚ) q := rfl

/-- Two points of the fundamental domain differing by a principal adele coincide. -/
theorem eq_of_sub_principal_mem_fundBox {x : AQ} {q q' : ℚ} (h : x - principal q ∈ fundBox)
    (h' : x - principal q' ∈ fundBox) : q' = q := by
  rw [← sub_eq_zero]
  obtain ⟨⟨h0, h1⟩, hf⟩ := h
  obtain ⟨⟨h0', h1'⟩, hf'⟩ := h'
  simp only [principal, Prod.fst_sub, RingHom.prod_apply, eq_ratCast] at h0 h1 h0' h1'
  apply eq_zero_of_integral_of_abs_lt_one
  · intro p hp
    obtain ⟨v, rfl⟩ := exists_pr_eq hp
    have := (v.adicCompletionIntegers ℚ).sub_mem (hf v) (hf' v)
    have e : (x - principal q).2 v - (x - principal q').2 v =
        algebraMap ℚ (v.adicCompletion ℚ) (q' - q) := by
      show (x.2 v - algebraMap ℚ Af q v) - (x.2 v - algebraMap ℚ Af q' v) = _
      rw [algebraMap_Af_apply, algebraMap_Af_apply, map_sub]
      ring
    rw [e] at this
    exact (algebraMap_mem_integers_iff v _).1 this
  · have : |((q' - q : ℚ) : ℝ)| < 1 := by
      rw [abs_lt]; push_cast; constructor <;> linarith
    exact_mod_cast this

/-- **GP3.** Every adele is uniquely a principal adele plus a point of `[0, 1) × ∏ ℤ_v`. -/
theorem existsUnique_sub_principal_mem_fundBox (x : AQ) :
    ∃! q : ℚ, x - principal q ∈ fundBox := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_sub_mem_integers x.2
  set n : ℤ := ⌊x.1 - q₁⌋
  have hq : x - principal (q₁ + n) ∈ fundBox := by
    refine ⟨?_, fun v => ?_⟩
    · simp only [principal, Prod.fst_sub, RingHom.prod_apply, eq_ratCast, Rat.cast_add,
        Rat.cast_intCast, Set.mem_Ico]
      constructor
      · have := Int.floor_le (x.1 - q₁); simp only [n] at *; linarith
      · have := Int.lt_floor_add_one (x.1 - q₁); simp only [n] at *; linarith
    · have e : (x - principal (q₁ + n)).2 v =
          (x.2 v - algebraMap ℚ (v.adicCompletion ℚ) q₁) - algebraMap ℚ (v.adicCompletion ℚ) n := by
        show x.2 v - algebraMap ℚ Af (q₁ + n) v = _
        rw [algebraMap_Af_apply, map_add]
        ring
      rw [e]
      exact (v.adicCompletionIntegers ℚ).sub_mem (hq₁ v) (intCast_mem_integers v n)
  exact ⟨q₁ + n, hq, fun q' hq' => eq_of_sub_principal_mem_fundBox hq hq'⟩

/-- The local integers `{x : |x|_v ≤ 1}` are compact. -/
theorem isCompact_integers_v (v : HeightOneSpectrum ℤ) :
    IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) := by
  have : (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) =
      (adicCompletion.padicEquiv v).symm '' Metric.closedBall (0 : ℚ_[pr v]) 1 := by
    ext x
    simp only [SetLike.mem_coe, mem_integers_iff, lnorm, Set.mem_image, Metric.mem_closedBall,
      dist_zero_right]
    constructor
    · intro hx; exact ⟨_, hx, (adicCompletion.padicEquiv v).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩; simpa using hy
  rw [this]
  exact (isCompact_closedBall _ _).image (adicCompletion.padicEquiv v).symm.continuous

instance (v : HeightOneSpectrum ℤ) : CompactSpace (v.adicCompletionIntegers ℚ) :=
  isCompact_iff_compactSpace.mp (isCompact_integers_v v)

/-- `∏ ℤ_v` is compact in the finite adeles. -/
theorem isCompact_intBox : IsCompact intBox := by
  have heq : intBox = incl '' Set.univ := by
    ext a
    simp only [intBox, Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    constructor
    · intro ha; exact ⟨fun v => ⟨a v, ha v⟩, rfl⟩
    · rintro ⟨x, rfl⟩ v; rw [incl_apply]; exact (x v).2
  rw [heq]
  exact isCompact_univ.image continuous_incl

/-- **GP2.** The quotient of the adeles by the principal adeles is compact. -/
theorem principal_cocompact : CompactSpace (AQ ⧸ principalSubgroup) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ intBox) := isCompact_Icc.prod isCompact_intBox
  refine ⟨?_⟩
  have : (Set.univ : Set (AQ ⧸ principalSubgroup)) =
      (QuotientAddGroup.mk : AQ → AQ ⧸ principalSubgroup) '' (Set.Icc (0 : ℝ) 1 ×ˢ intBox) := by
    refine (Set.eq_univ_of_forall fun c => ?_).symm
    induction c using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨q, hq, -⟩ := existsUnique_sub_principal_mem_fundBox x
      refine ⟨x - principal q, ⟨Set.Ico_subset_Icc_self hq.1, hq.2⟩, ?_⟩
      rw [QuotientAddGroup.eq]
      simp only [neg_sub]
      exact ⟨q, by simp⟩
  rw [this]
  exact hK.image QuotientAddGroup.continuous_mk

end GlobalTate.Poisson
