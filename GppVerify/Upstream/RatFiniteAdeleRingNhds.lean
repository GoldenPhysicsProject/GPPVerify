/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.Upstream.RatFiniteAdeleRingLattice

/-!
# The lattices `N ∏ ℤ_v` form a neighbourhood basis of `0` in the finite adeles of `ℚ`

Mathlib-only, in Mathlib's naming, for upstreaming.

* `Rat.FiniteAdeleRing.exists_natMulIntegral_subset`: every open neighbourhood of `0` in
  `FiniteAdeleRing ℤ ℚ` contains `N ∏ ℤ_v` for some positive integer `N`.

The proof pulls the neighbourhood back along `RestrictedProduct.structureMap` to an open set of the
product `∏ ℤ_v`, takes a basic box (finitely many coordinates constrained), and uses that at each
constrained place the neighbourhood contains `p^k ℤ_p`.
-/

open IsDedekindDomain Rat.HeightOneSpectrum

namespace Rat.FiniteAdeleRing

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

local notation "𝔸f" => FiniteAdeleRing ℤ ℚ

/-- Local statement: an open neighbourhood of `0` in `ℤ_v` contains every `x` with `‖x‖ ≤ p^{-k}`
for some `k`. -/
theorem exists_pow_norm_le_mem_of_isOpen (v : HeightOneSpectrum ℤ)
    {u : Set (v.adicCompletionIntegers ℚ)} (hu : IsOpen u) (h0 : (0 : v.adicCompletionIntegers ℚ) ∈ u) :
    ∃ k : ℕ, ∀ x : v.adicCompletionIntegers ℚ,
      ‖adicCompletion.padicEquiv v (x : v.adicCompletion ℚ)‖ ≤
        ((primesEquiv v : ℕ) : ℝ) ^ (-(k : ℤ)) → x ∈ u := by
  have hA : IsOpen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Valued.isOpen_integer _
  have hu' : IsOpen (Subtype.val '' u : Set (v.adicCompletion ℚ)) :=
    hA.isOpenMap_subtype_val u hu
  set e := adicCompletion.padicEquiv v with he
  have hopen : IsOpen (e '' (Subtype.val '' u)) := e.toHomeomorph.isOpenMap _ hu'
  have h0' : (0 : ℚ_[(primesEquiv v : ℕ)]) ∈ e '' (Subtype.val '' u) :=
    ⟨0, ⟨0, h0, rfl⟩, map_zero _⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 h0'
  have hp : (1 : ℝ) < (primesEquiv v : ℕ) := Nat.one_lt_cast.mpr (primesEquiv v).2.one_lt
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hp)
  refine ⟨k, fun x hx => ?_⟩
  have hlt : ‖e (x : v.adicCompletion ℚ)‖ < ε := by
    refine lt_of_le_of_lt hx ?_
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hk
  have hmem : e (x : v.adicCompletion ℚ) ∈ e '' (Subtype.val '' u) :=
    hball (Metric.mem_ball.2 (by rw [dist_zero_right]; exact hlt))
  obtain ⟨y, ⟨x', hx', rfl⟩, hy⟩ := hmem
  have : x' = x := Subtype.ext (e.injective hy)
  rwa [this] at hx'

/-- **The lattices `N ∏ ℤ_v` form a neighbourhood basis of `0`**: every open set containing `0`
contains `N ∏ ℤ_v` for some positive integer `N`. -/
theorem exists_natMulIntegral_subset {W : Set 𝔸f} (hW : IsOpen W) (h0 : (0 : 𝔸f) ∈ W) :
    ∃ N : ℕ, N ≠ 0 ∧ natMulIntegral N ⊆ W := by
  classical
  let A : (v : HeightOneSpectrum ℤ) → Set (v.adicCompletion ℚ) :=
    fun v => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  let φ := RestrictedProduct.structureMap (fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ) A
    Filter.cofinite
  have hφ : Continuous φ :=
    (RestrictedProduct.isEmbedding_structureMap (R := fun v : HeightOneSpectrum ℤ => v.adicCompletion ℚ)
      (A := A) (𝓕 := Filter.cofinite)).continuous
  have hopen : IsOpen (φ ⁻¹' W) := hW.preimage hφ
  have h0mem : (0 : (v : HeightOneSpectrum ℤ) → A v) ∈ φ ⁻¹' W := h0
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0mem
  have hk : ∀ v : HeightOneSpectrum ℤ, ∃ k : ℕ, v ∈ I → ∀ x : A v,
      ‖adicCompletion.padicEquiv v (x : v.adicCompletion ℚ)‖ ≤
        ((primesEquiv v : ℕ) : ℝ) ^ (-(k : ℤ)) → x ∈ u v := by
    intro v
    by_cases hv : v ∈ I
    · obtain ⟨k, hk⟩ := exists_pow_norm_le_mem_of_isOpen v (hu v hv).1 (hu v hv).2
      exact ⟨k, fun _ => hk⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose k hk using hk
  set N : ℕ := ∏ v ∈ I, (primesEquiv v : ℕ) ^ k v with hN
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (primesEquiv v).2.ne_zero
  refine ⟨N, hN0, fun f hf => ?_⟩
  have hfZ : f ∈ integralAdeles := natMulIntegral_subset hN0 hf
  let y : (v : HeightOneSpectrum ℤ) → A v := fun v => ⟨f v, hfZ v⟩
  have hφy : φ y = f := by
    apply RestrictedProduct.ext
    intro v
    rfl
  have hy : y ∈ (I : Set (HeightOneSpectrum ℤ)).pi u := by
    intro v hv
    refine hk v hv (y v) ?_
    -- `f v = N * (N⁻¹ f) v`
    have hfe : f = (N : 𝔸f) * (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f) := by
      rw [← mul_assoc, natCast_mul_algebraMap_inv hN0, one_mul]
    have hz : (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f) v ∈ v.adicCompletionIntegers ℚ := hf v
    have hfv : f v = ((N : ℕ) : v.adicCompletion ℚ) * (algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f) v := by
      conv_lhs => rw [hfe]
      have : ((N : 𝔸f)) v = ((N : ℕ) : v.adicCompletion ℚ) := by
        have : (N : 𝔸f) = algebraMap ℚ 𝔸f (N : ℚ) := by simp
        rw [this]
        exact map_natCast (algebraMap ℚ (v.adicCompletion ℚ)) N
      rw [← this]
      rfl
    show ‖adicCompletion.padicEquiv v (f v)‖ ≤ _
    rw [hfv, map_mul, norm_mul, map_natCast]
    have hz1 : ‖adicCompletion.padicEquiv v ((algebraMap ℚ 𝔸f ((N : ℚ)⁻¹) * f) v)‖ ≤ 1 :=
      (mem_adicCompletionIntegers_iff v _).1 hz
    have hdvd : (primesEquiv v : ℕ) ^ k v ∣ N :=
      Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum ℤ => (primesEquiv v : ℕ) ^ k v) hv
    obtain ⟨m, hm⟩ := hdvd
    have hNn : ‖((N : ℕ) : ℚ_[(primesEquiv v : ℕ)])‖ ≤
        ((primesEquiv v : ℕ) : ℝ) ^ (-(k v : ℤ)) := by
      rw [hm, Nat.cast_mul, Nat.cast_pow]
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
      have hm1 : ‖((m : ℕ) : ℚ_[(primesEquiv v : ℕ)])‖ ≤ 1 := by
        have h := Padic.norm_int_le_one (p := (primesEquiv v : ℕ)) (m : ℤ)
        rwa [Int.cast_natCast] at h
      exact mul_le_of_le_one_right (by positivity) hm1
    exact (mul_le_of_le_one_right (norm_nonneg _) hz1).trans hNn
  have h : φ y ∈ W := hsub hy
  rwa [hφy] at h

end Rat.FiniteAdeleRing
