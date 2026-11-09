/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.Upstream.RatFiniteAdeleRingNhds

/-!
# Locally constant, compactly supported functions on the finite adeles of `ℚ`

Mathlib-only, in Mathlib's naming, for upstreaming.

A locally constant function with compact support on `𝔸_{ℚ,f}` is *uniformly* locally constant (it
is invariant under translation by `N ∏ ℤ_v` for some positive integer `N`) and is a finite linear
combination of indicators of cosets of `N ∏ ℤ_v`.

* `Rat.FiniteAdeleRing.natMulIntegralAddSubgroup N`: the subgroup `N ∏ ℤ_v`.
* `Rat.FiniteAdeleRing.exists_uniform_of_isLocallyConstant`: uniform local constancy.
* `Rat.FiniteAdeleRing.exists_eq_sum_fiber_of_isLocallyConstant`: the finite decomposition into
  indicators of the fibers of `𝔸_{ℚ,f} → 𝔸_{ℚ,f} / N ∏ ℤ_v`.
-/

open IsDedekindDomain

namespace Rat.FiniteAdeleRing

local notation "𝔸f" => FiniteAdeleRing ℤ ℚ

/-- The subgroup `N ∏ ℤ_v` of the finite adeles. -/
def natMulIntegralAddSubgroup (N : ℕ) : AddSubgroup 𝔸f where
  carrier := natMulIntegral N
  zero_mem' := by
    show algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * 0 ∈ integralAdeles
    rw [mul_zero]; exact zero_mem_integralAdeles
  add_mem' := add_mem_natMulIntegral
  neg_mem' := neg_mem_natMulIntegral

theorem mem_natMulIntegralAddSubgroup {N : ℕ} {f : 𝔸f} :
    f ∈ natMulIntegralAddSubgroup N ↔ f ∈ natMulIntegral N := Iff.rfl

/-- `M ∏ ℤ_v ⊆ N ∏ ℤ_v` when `N ∣ M`. -/
theorem natMulIntegral_subset_of_dvd {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (h : N ∣ M) :
    natMulIntegral M ⊆ natMulIntegral N := by
  intro f hf
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := by rintro rfl; simp at hM
  -- `(1/N) f = c · (1/(N c)) f`
  have e : algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f =
      (c : 𝔸f) * (algebraMap ℚ 𝔸f (((N * c : ℕ) : ℚ)⁻¹) * f) := by
    rw [← mul_assoc]
    congr 1
    rw [← map_natCast (algebraMap ℚ 𝔸f) c, ← map_mul]
    congr 1
    push_cast
    have : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    have : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    field_simp
  show algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f ∈ integralAdeles
  rw [e]
  exact mul_mem_integralAdeles (natCast_mem_integralAdeles c) hf

/-- **Uniform local constancy.** A locally constant function with compact support is invariant
under translation by `N ∏ ℤ_v` for some positive integer `N`. -/
theorem exists_uniform_of_isLocallyConstant {α : Type*} [Zero α] {g : 𝔸f → α}
    (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x := by
  classical
  -- per-point radius
  have hpt : ∀ x : 𝔸f, ∃ N : ℕ, N ≠ 0 ∧ ∀ u ∈ natMulIntegral N, g (x + u) = g x := by
    intro x
    have hopen : IsOpen ((fun u : 𝔸f => x + u) ⁻¹' {y | g y = g x}) :=
      (hg.isOpen_fiber (g x)).preimage (continuous_const.add continuous_id)
    obtain ⟨N, hN, hsub⟩ := exists_natMulIntegral_subset hopen (by simp)
    exact ⟨N, hN, fun u hu => hsub hu⟩
  choose N hN0 hN using hpt
  let T : 𝔸f → Set 𝔸f := fun x => {y | y - x ∈ natMulIntegral (N x)}
  have hTopen : ∀ x, IsOpen (T x) := fun x =>
    (isOpen_natMulIntegral (N x)).preimage (continuous_id.sub continuous_const)
  have hxT : ∀ x, x ∈ T x := fun x => by
    show x - x ∈ natMulIntegral (N x)
    rw [sub_self]; exact (natMulIntegralAddSubgroup (N x)).zero_mem
  obtain ⟨t, -, hcov⟩ := IsCompact.elim_nhds_subcover hc T (fun x _ => (hTopen x).mem_nhds (hxT x))
  refine ⟨∏ x ∈ t, N x, Finset.prod_ne_zero_iff.2 fun x _ => hN0 x, fun y u hu => ?_⟩
  -- the case `y ∈ tsupport g`
  have key : ∀ y u, u ∈ natMulIntegral (∏ x ∈ t, N x) → y ∈ tsupport g → g (y + u) = g y := by
    intro y u hu hy
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcov hy)
    have hdvd : N x ∣ ∏ x ∈ t, N x := Finset.dvd_prod_of_mem N hxt
    have hM : (∏ x ∈ t, N x) ≠ 0 := Finset.prod_ne_zero_iff.2 fun x _ => hN0 x
    have hu' : u ∈ natMulIntegral (N x) := natMulIntegral_subset_of_dvd (hN0 x) hM hdvd hu
    have hyx' : y - x ∈ natMulIntegral (N x) := hyx
    have h1 : g y = g x := by
      have h := hN x (y - x) hyx'
      rwa [add_sub_cancel] at h
    have h2 : g (y + u) = g x := by
      have hw : y + u - x ∈ natMulIntegral (N x) := by
        have h := add_mem_natMulIntegral hyx' hu'
        rwa [sub_add_eq_add_sub] at h
      have h := hN x (y + u - x) hw
      rwa [add_sub_cancel] at h
    rw [h1, h2]
  by_cases hy : y ∈ tsupport g
  · exact key y u hu hy
  · by_cases hyu : y + u ∈ tsupport g
    · have h := key (y + u) (-u) (neg_mem_natMulIntegral hu) hyu
      rw [add_neg_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

open Classical in
/-- **Finite decomposition into coset indicators, for a given uniformity modulus.** If `g` has
compact support and is invariant under translation by `N ∏ ℤ_v`, it is a finite sum, over classes
`c` of `𝔸_{ℚ,f} / N ∏ ℤ_v`, of its value on a representative of `c` times the indicator of the
class. -/
theorem exists_eq_sum_fiber_of_uniform {α : Type*} [AddCommMonoid α] {g : 𝔸f → α}
    (hc : HasCompactSupport g) {N : ℕ}
    (huni : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x) :
    ∃ F : Finset (𝔸f ⧸ natMulIntegralAddSubgroup N),
      ∀ y : 𝔸f, g y = ∑ c ∈ F, if (y : 𝔸f ⧸ natMulIntegralAddSubgroup N) = c then g c.out else 0 := by
  set H := natMulIntegralAddSubgroup N with hH
  let T : 𝔸f → Set 𝔸f := fun x => {y | y - x ∈ natMulIntegral N}
  have hTopen : ∀ x, IsOpen (T x) := fun x =>
    (isOpen_natMulIntegral N).preimage (continuous_id.sub continuous_const)
  have hxT : ∀ x, x ∈ T x := fun x => by
    show x - x ∈ natMulIntegral N
    rw [sub_self]; exact H.zero_mem
  obtain ⟨t, -, hcov⟩ := IsCompact.elim_nhds_subcover hc T
    (fun x _ => (hTopen x).mem_nhds (hxT x))
  refine ⟨t.image (QuotientAddGroup.mk : 𝔸f → 𝔸f ⧸ H), fun y => ?_⟩
  by_cases hy : (y : 𝔸f ⧸ H) ∈ t.image (QuotientAddGroup.mk : 𝔸f → 𝔸f ⧸ H)
  · rw [Finset.sum_eq_single_of_mem _ hy]
    · rw [if_pos rfl]
      -- the chosen representative differs from `y` by an element of `H`
      have hq : ((y : 𝔸f ⧸ H)).out = ((y : 𝔸f ⧸ H)).out := rfl
      have hout : (((y : 𝔸f ⧸ H).out : 𝔸f) : 𝔸f ⧸ H) = (y : 𝔸f ⧸ H) := Quotient.out_eq _
      have hmem : -y + (y : 𝔸f ⧸ H).out ∈ H := by
        rw [← QuotientAddGroup.eq]; exact hout.symm
      have := huni y (-y + (y : 𝔸f ⧸ H).out) hmem
      rw [add_neg_cancel_left] at this
      exact this.symm
    · intro c _ hne
      rw [if_neg]
      exact fun h => hne h.symm
  · rw [Finset.sum_eq_zero]
    · by_contra hne
      have hysupp : y ∈ tsupport g := subset_tsupport g (Function.mem_support.2 hne)
      obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (hcov hysupp)
      apply hy
      refine Finset.mem_image.2 ⟨x, hxt, ?_⟩
      have hyx' : y - x ∈ natMulIntegral N := hyx
      rw [QuotientAddGroup.eq, neg_add_eq_sub]
      exact hyx'
    · intro c hc'
      rw [if_neg]
      rintro rfl
      exact hy hc'

open Classical in
/-- **Finite decomposition into coset indicators.** A locally constant function with compact support
on `𝔸_{ℚ,f}` is a finite sum, over classes `c` of `𝔸_{ℚ,f} / N ∏ ℤ_v`, of its value on a
representative of `c` times the indicator of the class. -/
theorem exists_eq_sum_fiber_of_isLocallyConstant {α : Type*} [AddCommMonoid α] {g : 𝔸f → α}
    (hg : IsLocallyConstant g) (hc : HasCompactSupport g) :
    ∃ (N : ℕ) (_ : N ≠ 0) (F : Finset (𝔸f ⧸ natMulIntegralAddSubgroup N)),
      ∀ y : 𝔸f, g y = ∑ c ∈ F, if (y : 𝔸f ⧸ natMulIntegralAddSubgroup N) = c then g c.out else 0 := by
  obtain ⟨N, hN0, huni⟩ := exists_uniform_of_isLocallyConstant hg hc
  obtain ⟨F, hF⟩ := exists_eq_sum_fiber_of_uniform hc huni
  exact ⟨N, hN0, F, hF⟩

/-- Every finite adele lies in `(1/M) ∏ ℤ_v` for some positive integer `M` (a consequence of strong
approximation: `f = q + z` with `q ∈ ℚ`, `z` integral, and `M = q.den`). -/
theorem exists_natCast_mul_mem_integralAdeles (f : 𝔸f) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : 𝔸f) * f ∈ integralAdeles := by
  obtain ⟨q, hq⟩ := exists_rat_sub_mem_integralAdeles' f
  refine ⟨q.den, q.den_nz, ?_⟩
  have e : (q.den : 𝔸f) * f = algebraMap ℚ 𝔸f ((q.num : ℤ) : ℚ) +
      (q.den : 𝔸f) * (f - algebraMap ℚ 𝔸f q) := by
    have h1 : algebraMap ℚ 𝔸f ((q.num : ℤ) : ℚ) = (q.den : 𝔸f) * algebraMap ℚ 𝔸f q := by
      rw [← map_natCast (algebraMap ℚ 𝔸f) q.den, ← map_mul, Rat.den_mul_eq_num]
    rw [h1]; ring
  rw [e]
  refine add_mem_integralAdeles ?_ (mul_mem_integralAdeles (natCast_mem_integralAdeles _) hq)
  have : algebraMap ℚ 𝔸f ((q.num : ℤ) : ℚ) = ((q.num : ℤ) : 𝔸f) := by simp
  rw [this]; exact intCast_mem_integralAdeles _

/-- A function invariant under translation by `N ∏ ℤ_v` is locally constant. -/
theorem isLocallyConstant_of_uniform {α : Type*} {g : 𝔸f → α} {N : ℕ}
    (huni : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x) : IsLocallyConstant g := by
  rw [IsLocallyConstant.iff_isOpen_fiber_apply]
  intro x
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hopen : IsOpen ((fun z : 𝔸f => z - y) ⁻¹' natMulIntegral N) :=
    (isOpen_natMulIntegral N).preimage (continuous_id.sub continuous_const)
  have h0 : y ∈ (fun z : 𝔸f => z - y) ⁻¹' natMulIntegral N := by
    show y - y ∈ natMulIntegral N
    rw [sub_self]; exact (natMulIntegralAddSubgroup N).zero_mem
  filter_upwards [hopen.mem_nhds h0] with z hz
  have h := huni y (z - y) hz
  rw [add_sub_cancel] at h
  show g z = g x
  rw [h]; exact hy

/-- `(1/N) ∏ ℤ_v` is compact. -/
theorem isCompact_integralDivNat {N : ℕ} (hN : N ≠ 0) : IsCompact (integralDivNat N) := by
  have : integralDivNat N =
      (fun x : 𝔸f => algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * x) '' integralAdeles := by
    ext x
    constructor
    · intro hx
      refine ⟨(N : 𝔸f) * x, hx, ?_⟩
      show algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * ((N : 𝔸f) * x) = x
      rw [← mul_assoc, mul_comm _ (N : 𝔸f), natCast_mul_algebraMap_inv hN, one_mul]
    · rintro ⟨z, hz, rfl⟩
      show (N : 𝔸f) * (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * z) ∈ integralAdeles
      rw [← mul_assoc, natCast_mul_algebraMap_inv hN, one_mul]; exact hz
  rw [this]
  exact isCompact_integralAdeles.image (continuous_const.mul continuous_id)

/-- A uniformity modulus can be replaced by any positive multiple. -/
theorem uniform_of_dvd {α : Type*} {g : 𝔸f → α} {N M : ℕ} (hN : N ≠ 0) (hM : M ≠ 0) (h : N ∣ M)
    (huni : ∀ x, ∀ u ∈ natMulIntegral N, g (x + u) = g x) :
    ∀ x, ∀ u ∈ natMulIntegral M, g (x + u) = g x :=
  fun x u hu => huni x u (natMulIntegral_subset_of_dvd hN hM h hu)

end Rat.FiniteAdeleRing
