/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.Upstream.RatFiniteAdeleRingApprox

/-!
# The lattices `N ∏ ℤ_v` and `(1/N) ∏ ℤ_v` in the finite adeles of `ℚ`

Mathlib-only, in Mathlib's naming, for upstreaming.

For a positive integer `N`, `natMulIntegral N = N · ∏_v ℤ_v` is an open compact subgroup of
`𝔸_{ℚ,f}` of index `N` in `∏_v ℤ_v`, and `integralDivNat N = (1/N) ∏_v ℤ_v` contains `∏_v ℤ_v` with
index `N`. The key input is strong approximation, which gives the coset decomposition
`∏_v ℤ_v = ⊔_{r < N} (r + N ∏_v ℤ_v)` (`exists_natCast_sub_mem_natMulIntegral` and
`natCast_sub_mem_natMulIntegral_iff`). Consequently, for the Haar measure of
`RatFiniteAdeleRingHaar.lean`,

* `haar_natMulIntegral : haar (natMulIntegral N) = (N : ℝ≥0∞)⁻¹`,
* `haar_integralDivNat : haar (integralDivNat N) = N`.
-/

open IsDedekindDomain MeasureTheory

namespace Rat.FiniteAdeleRing

local notation "𝔸f" => FiniteAdeleRing ℤ ℚ

/-! ### The ring `∏ ℤ_v` -/

theorem add_mem_integralAdeles {a b : 𝔸f} (ha : a ∈ integralAdeles) (hb : b ∈ integralAdeles) :
    a + b ∈ integralAdeles := fun v => add_mem (ha v) (hb v)

theorem neg_mem_integralAdeles {a : 𝔸f} (ha : a ∈ integralAdeles) : -a ∈ integralAdeles :=
  fun v => neg_mem (ha v)

theorem sub_mem_integralAdeles {a b : 𝔸f} (ha : a ∈ integralAdeles) (hb : b ∈ integralAdeles) :
    a - b ∈ integralAdeles := fun v => sub_mem (ha v) (hb v)

theorem mul_mem_integralAdeles {a b : 𝔸f} (ha : a ∈ integralAdeles) (hb : b ∈ integralAdeles) :
    a * b ∈ integralAdeles := fun v => mul_mem (ha v) (hb v)

theorem intCast_mem_integralAdeles (n : ℤ) : (n : 𝔸f) ∈ integralAdeles := by
  intro v
  have : (n : 𝔸f) = algebraMap ℚ 𝔸f (n : ℚ) := by simp
  rw [this]
  exact intCast_mem_adicCompletionIntegers v n

theorem natCast_mem_integralAdeles (n : ℕ) : (n : 𝔸f) ∈ integralAdeles := by
  simpa using intCast_mem_integralAdeles (n : ℤ)

/-- A rational whose diagonal image is everywhere integral is its numerator. -/
theorem eq_num_of_algebraMap_mem_integralAdeles {q : ℚ}
    (h : algebraMap ℚ 𝔸f q ∈ integralAdeles) : q = q.num :=
  eq_num_of_forall_mem_adicCompletionIntegers q h

/-! ### The lattices -/

/-- `N · ∏ ℤ_v`. -/
def natMulIntegral (N : ℕ) : Set 𝔸f :=
  {f | algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f ∈ integralAdeles}

/-- `(1/N) · ∏ ℤ_v`. -/
def integralDivNat (N : ℕ) : Set 𝔸f := {f | (N : 𝔸f) * f ∈ integralAdeles}

theorem isOpen_natMulIntegral (N : ℕ) : IsOpen (natMulIntegral N) :=
  (continuous_const.mul continuous_id).isOpen_preimage _ isOpen_integralAdeles

theorem isOpen_integralDivNat (N : ℕ) : IsOpen (integralDivNat N) :=
  (continuous_const.mul continuous_id).isOpen_preimage _ isOpen_integralAdeles

variable {N : ℕ}

theorem natCast_mul_algebraMap_inv (hN : N ≠ 0) :
    (N : 𝔸f) * algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) = 1 := by
  rw [← map_natCast (algebraMap ℚ 𝔸f) N, ← map_mul, mul_inv_cancel₀ (by exact_mod_cast hN),
    map_one]

theorem natMulIntegral_subset (hN : N ≠ 0) : natMulIntegral N ⊆ integralAdeles := by
  intro f hf
  have : f = (N : 𝔸f) * (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f) := by
    rw [← mul_assoc, natCast_mul_algebraMap_inv hN, one_mul]
  rw [this]
  exact mul_mem_integralAdeles (natCast_mem_integralAdeles N) hf

theorem integralAdeles_subset_integralDivNat : integralAdeles ⊆ integralDivNat N :=
  fun _ hz => mul_mem_integralAdeles (natCast_mem_integralAdeles N) hz

theorem add_mem_natMulIntegral {a b : 𝔸f} (ha : a ∈ natMulIntegral N)
    (hb : b ∈ natMulIntegral N) : a + b ∈ natMulIntegral N := by
  show _ * (a + b) ∈ integralAdeles
  rw [mul_add]
  exact add_mem_integralAdeles ha hb

theorem neg_mem_natMulIntegral {a : 𝔸f} (ha : a ∈ natMulIntegral N) : -a ∈ natMulIntegral N := by
  show _ * (-a) ∈ integralAdeles
  rw [mul_neg]
  exact neg_mem_integralAdeles ha

theorem sub_mem_natMulIntegral {a b : 𝔸f} (ha : a ∈ natMulIntegral N)
    (hb : b ∈ natMulIntegral N) : a - b ∈ natMulIntegral N := by
  rw [sub_eq_add_neg]
  exact add_mem_natMulIntegral ha (neg_mem_natMulIntegral hb)

/-- An integer lies in `N ∏ ℤ_v` iff `N` divides it. -/
theorem intCast_mem_natMulIntegral_iff (hN : N ≠ 0) (m : ℤ) :
    (m : 𝔸f) ∈ natMulIntegral N ↔ (N : ℤ) ∣ m := by
  have e : algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (m : 𝔸f) = algebraMap ℚ 𝔸f ((N : ℚ)⁻¹ * m) := by
    simp
  show algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (m : 𝔸f) ∈ integralAdeles ↔ _
  rw [e]
  constructor
  · intro h
    have hq := eq_num_of_algebraMap_mem_integralAdeles h
    refine ⟨((N : ℚ)⁻¹ * m).num, ?_⟩
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    have : (m : ℚ) = N * ((N : ℚ)⁻¹ * m).num := by
      rw [← hq]; field_simp
    exact_mod_cast this
  · rintro ⟨k, rfl⟩
    have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
    have : (N : ℚ)⁻¹ * (((N : ℤ) * k : ℤ) : ℚ) = (k : ℚ) := by push_cast; field_simp
    rw [this]
    have := intCast_mem_integralAdeles k
    simpa using this

/-- **Coset representatives** (strong approximation): every `z ∈ ∏ ℤ_v` is congruent to a unique
`r < N` modulo `N ∏ ℤ_v`. Existence. -/
theorem exists_natCast_sub_mem_natMulIntegral (hN : N ≠ 0) {z : 𝔸f} (hz : z ∈ integralAdeles) :
    ∃ r : ℕ, r < N ∧ z - (r : 𝔸f) ∈ natMulIntegral N := by
  obtain ⟨q, hq⟩ := exists_rat_sub_mem_integralAdeles' (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * z)
  have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  -- `z - N q ∈ N ∏ ℤ_v`
  have h1 : z - algebraMap ℚ 𝔸f ((N : ℚ) * q) ∈ natMulIntegral N := by
    show _ * _ ∈ integralAdeles
    have : algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (z - algebraMap ℚ 𝔸f ((N : ℚ) * q)) =
        algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * z - algebraMap ℚ 𝔸f q := by
      rw [mul_sub, ← map_mul, inv_mul_cancel_left₀ hN']
    rw [this]; exact hq
  have h2 : algebraMap ℚ 𝔸f ((N : ℚ) * q) ∈ integralAdeles := by
    have := sub_mem_integralAdeles hz (natMulIntegral_subset hN h1)
    simpa using this
  have h3 := eq_num_of_algebraMap_mem_integralAdeles h2
  set n : ℤ := ((N : ℚ) * q).num with hn
  -- reduce `n` modulo `N`
  refine ⟨(n % (N : ℤ)).toNat, ?_, ?_⟩
  · have := Int.emod_nonneg n (show (N : ℤ) ≠ 0 by exact_mod_cast hN)
    have := Int.emod_lt_of_pos n (show (0 : ℤ) < N by exact_mod_cast Nat.pos_of_ne_zero hN)
    omega
  · have hr : (((n % (N : ℤ)).toNat : ℕ) : ℤ) = n % (N : ℤ) :=
      Int.toNat_of_nonneg (Int.emod_nonneg n (by exact_mod_cast hN))
    have hnN : (n : 𝔸f) = ((n % (N : ℤ) : ℤ) : 𝔸f) + ((N : ℤ) * (n / (N : ℤ)) : ℤ) := by
      rw [← Int.cast_add, Int.emod_add_mul_ediv]
    have hz' : z - (((n % (N : ℤ)).toNat : ℕ) : 𝔸f) =
        (z - algebraMap ℚ 𝔸f ((N : ℚ) * q)) + (((N : ℤ) * (n / (N : ℤ)) : ℤ) : 𝔸f) := by
      have e1 : algebraMap ℚ 𝔸f ((N : ℚ) * q) = (n : 𝔸f) := by
        rw [h3]; simp [hn]
      have e2 : (((n % (N : ℤ)).toNat : ℕ) : 𝔸f) = ((n % (N : ℤ) : ℤ) : 𝔸f) := by
        have : (((n % (N : ℤ)).toNat : ℕ) : 𝔸f) = ((((n % (N : ℤ)).toNat : ℕ) : ℤ) : 𝔸f) :=
          (Int.cast_natCast _).symm
        rw [this, hr]
      rw [e1, e2, hnN]; ring
    rw [hz']
    exact add_mem_natMulIntegral h1 ((intCast_mem_natMulIntegral_iff hN _).2 (dvd_mul_right _ _))

/-- Uniqueness of the coset representative. -/
theorem natCast_sub_mem_natMulIntegral_iff (hN : N ≠ 0) {r r' : ℕ} (hr : r < N) (hr' : r' < N) :
    ((r : 𝔸f) - (r' : 𝔸f) ∈ natMulIntegral N) ↔ r = r' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  swap
  · rw [h, sub_self]
    intro v
    simp only [mul_zero]
    exact zero_mem _
  have e : ((r : 𝔸f) - (r' : 𝔸f)) = (((r : ℤ) - r' : ℤ) : 𝔸f) := by push_cast; ring
  rw [e, intCast_mem_natMulIntegral_iff hN] at h
  obtain ⟨k, hk⟩ := h
  have hN0 : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hr2 : (r : ℤ) < N := by exact_mod_cast hr
  have hr2' : (r' : ℤ) < N := by exact_mod_cast hr'
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  rw [hk0, mul_zero] at hk
  omega

/-! ### Haar volumes -/

/-- The coset `r + N ∏ ℤ_v`. -/
def natMulIntegralCoset (N r : ℕ) : Set 𝔸f := {f | f - (r : 𝔸f) ∈ natMulIntegral N}

theorem isOpen_natMulIntegralCoset (N r : ℕ) : IsOpen (natMulIntegralCoset N r) :=
  (isOpen_natMulIntegral N).preimage (continuous_id.sub continuous_const)

theorem haar_natMulIntegralCoset (N r : ℕ) :
    haar (natMulIntegralCoset N r) = haar (natMulIntegral N) := by
  have : natMulIntegralCoset N r = (fun f : 𝔸f => f + -(r : 𝔸f)) ⁻¹' natMulIntegral N := by
    ext f; simp [natMulIntegralCoset, sub_eq_add_neg]
  rw [this]
  exact measure_preimage_add_right haar _ _

theorem integralAdeles_eq_iUnion_cosets (hN : N ≠ 0) :
    integralAdeles = ⋃ r ∈ Finset.range N, natMulIntegralCoset N r := by
  ext f
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hf
    obtain ⟨r, hr, h⟩ := exists_natCast_sub_mem_natMulIntegral hN hf
    exact ⟨r, hr, h⟩
  · rintro ⟨r, -, h⟩
    have := add_mem_integralAdeles (natMulIntegral_subset hN h) (natCast_mem_integralAdeles r)
    simpa using this

theorem pairwiseDisjoint_natMulIntegralCoset (hN : N ≠ 0) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (natMulIntegralCoset N) := by
  intro r hr r' hr' hne
  refine Set.disjoint_left.2 fun f hf hf' => hne ?_
  have hrN : r < N := Finset.mem_range.1 hr
  have hr'N : r' < N := Finset.mem_range.1 hr'
  have h1 : f - (r : 𝔸f) ∈ natMulIntegral N := hf
  have h2 : f - (r' : 𝔸f) ∈ natMulIntegral N := hf'
  have h3 : (r : 𝔸f) - (r' : 𝔸f) ∈ natMulIntegral N := by
    have := sub_mem_natMulIntegral h2 h1
    rwa [sub_sub_sub_cancel_left] at this
  exact (natCast_sub_mem_natMulIntegral_iff hN hrN hr'N).1 h3

/-- `∏ ℤ_v` is the disjoint union of the `N` cosets of `N ∏ ℤ_v`, so `N ∏ ℤ_v` has volume `1/N`. -/
theorem haar_natMulIntegral (hN : N ≠ 0) : haar (natMulIntegral N) = (N : ENNReal)⁻¹ := by
  have h1 : haar integralAdeles = (N : ENNReal) * haar (natMulIntegral N) := by
    rw [integralAdeles_eq_iUnion_cosets hN,
      measure_biUnion_finset (pairwiseDisjoint_natMulIntegralCoset hN)
        (fun r _ => (isOpen_natMulIntegralCoset N r).measurableSet)]
    simp only [haar_natMulIntegralCoset, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [haar_integralAdeles] at h1
  exact ENNReal.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1.symm)

/-- The coset `r/N + ∏ ℤ_v` of `∏ ℤ_v` in `(1/N) ∏ ℤ_v`. -/
def integralDivNatCoset (N r : ℕ) : Set 𝔸f :=
  {f | f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f) ∈ integralAdeles}

theorem isOpen_integralDivNatCoset (N r : ℕ) : IsOpen (integralDivNatCoset N r) :=
  isOpen_integralAdeles.preimage (continuous_id.sub continuous_const)

theorem haar_integralDivNatCoset (N r : ℕ) :
    haar (integralDivNatCoset N r) = 1 := by
  have : integralDivNatCoset N r =
      (fun f : 𝔸f => f + -(algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f))) ⁻¹' integralAdeles := by
    ext f; simp [integralDivNatCoset, sub_eq_add_neg]
  rw [this, measure_preimage_add_right, haar_integralAdeles]

theorem integralDivNat_eq_iUnion_cosets (hN : N ≠ 0) :
    integralDivNat N = ⋃ r ∈ Finset.range N, integralDivNatCoset N r := by
  ext f
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · intro hf
    obtain ⟨r, hr, h⟩ := exists_natCast_sub_mem_natMulIntegral hN hf
    refine ⟨r, hr, ?_⟩
    have e : algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * ((N : 𝔸f) * f - (r : 𝔸f)) =
        f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f) := by
      rw [mul_sub, ← mul_assoc, mul_comm (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹)), natCast_mul_algebraMap_inv hN,
        one_mul]
    show f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f) ∈ integralAdeles
    rw [← e]
    exact h
  · rintro ⟨r, -, h⟩
    have e : (N : 𝔸f) * f = (N : 𝔸f) * (f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f)) + (r : 𝔸f) := by
      rw [mul_sub, ← mul_assoc, natCast_mul_algebraMap_inv hN, one_mul]; ring
    show (N : 𝔸f) * f ∈ integralAdeles
    rw [e]
    exact add_mem_integralAdeles (mul_mem_integralAdeles (natCast_mem_integralAdeles N) h)
      (natCast_mem_integralAdeles r)

theorem pairwiseDisjoint_integralDivNatCoset (hN : N ≠ 0) :
    (↑(Finset.range N) : Set ℕ).PairwiseDisjoint (integralDivNatCoset N) := by
  intro r hr r' hr' hne
  refine Set.disjoint_left.2 fun f hf hf' => hne ?_
  have hrN : r < N := Finset.mem_range.1 hr
  have hr'N : r' < N := Finset.mem_range.1 hr'
  have h1 : f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f) ∈ integralAdeles := hf
  have h2 : f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r' : 𝔸f) ∈ integralAdeles := hf'
  have h3 : (r : 𝔸f) - (r' : 𝔸f) ∈ natMulIntegral N := by
    have := sub_mem_integralAdeles h2 h1
    have e : f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r' : 𝔸f) -
        (f - algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * (r : 𝔸f)) =
        algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * ((r : 𝔸f) - (r' : 𝔸f)) := by
      rw [mul_sub]; abel
    rwa [e] at this
  exact (natCast_sub_mem_natMulIntegral_iff hN hrN hr'N).1 h3

/-- `(1/N) ∏ ℤ_v` is the disjoint union of `N` cosets of `∏ ℤ_v`, so it has volume `N`. -/
theorem haar_integralDivNat (hN : N ≠ 0) : haar (integralDivNat N) = N := by
  rw [integralDivNat_eq_iUnion_cosets hN,
    measure_biUnion_finset (pairwiseDisjoint_integralDivNatCoset hN)
      (fun r _ => (isOpen_integralDivNatCoset N r).measurableSet)]
  simp [haar_integralDivNatCoset]

end Rat.FiniteAdeleRing
