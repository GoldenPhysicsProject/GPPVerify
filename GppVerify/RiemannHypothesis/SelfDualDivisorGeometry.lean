import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.NumberTheory.Divisors

/-!
# The finite self-dual divisor geometry: subgroup Gram matrix and Möbius parity vector

Source: Codex, GPPDiscovery2 `research/2026-09-28_finite_selfdual_divisor_hodge_geometry.md`,
§§1, 3, 4, 6 (the Fourier-duality statement of §2 and the BSD/Hodge interpretations are not
formalized).

Identify `ℤ/Nℤ` with the residues `1, …, N`. For `d ∣ N` let `H_d` be the multiples of `d` and
`v_d = |H_d|^{-1/2} 1_{H_d}` its normalized state.

* `gram_eq`: `⟨v_d, v_e⟩ = gcd(d, e) / √(d e)` (since `H_d ∩ H_e = H_{lcm(d,e)}` and
  `|H_d| = N/d`): the critical arithmetic TFD/GCD kernel is the Gram matrix of finite-index
  sublattices;
* `overlap_prime`: `⟨v_d, v_{dp}⟩ = p^{-1/2}`: the critical factor `p^{-1/2}` is the cosine between
  a subgroup and its index-`p` sublattice;
* `mobius_eigen`: for a finite set `P` of primes, with the squarefree divisors `d_S = ∏_{p∈S} p`
  (`S ⊆ P`), the kernel is `K(d_T, d_S) = ∏_{p ∈ T △ S} p^{-1/2}` (`kern`), and the Möbius parity
  vector `μ(d_S) = (−1)^{|S|}` is an eigenvector,
  `Σ_{S⊆P} (−1)^{|S|} K(d_T, d_S) = (−1)^{|T|} ∏_{p∈P} (1 − p^{-1/2})`, i.e. eigenvalue
  `∏_{p∈P} (1 − p^{-1/2})`, which tends to `0` as `P` grows (the all-prime antisymmetric state).

## Checks and scope

All claims check. The tensor-product statement `K_N = ⨂ K_p` is the factorization
`kern T S = ∏_{p∈P} (local factor)`; the eigenvector computation is exactly its consequence and is
proved by induction on `P`, with the weights `w_p` left arbitrary (`mobius_eigen_weighted`).
**Not formalized:** the unitary Fourier duality `𝓕 v_d = v_{N/d}` (§2), the identification of the
divisor cube with a Hodge-star/Koszul complex (§§5, 9), and the limit statement
`∏_{p ≤ P}(1 − p^{-1/2}) → 0`. No RH claim.
-/

open Finset

namespace GppSelfDualDivisor

/-! ### The subgroup states and their Gram matrix -/

/-- The multiples of `d` among the residues `1, …, N`. -/
def Hset (N d : ℕ) : Finset ℕ := (Ioc 0 N).filter (d ∣ ·)

theorem card_Hset (N d : ℕ) : (Hset N d).card = N / d := Nat.Ioc_filter_dvd_card_eq_div N d

theorem Hset_inter (N d e : ℕ) : Hset N d ∩ Hset N e = Hset N (Nat.lcm d e) := by
  ext x
  simp only [Hset, mem_inter, mem_filter, Nat.lcm_dvd_iff]
  tauto

/-- The normalized subgroup state `v_d(x) = |H_d|^{-1/2} 1_{H_d}(x)`. -/
noncomputable def vstate (N d x : ℕ) : ℝ :=
  if d ∣ x then 1 / Real.sqrt ((N / d : ℕ) : ℝ) else 0

/-- The Gram pairing of two subgroup states. -/
noncomputable def gram (N d e : ℕ) : ℝ := ∑ x ∈ Ioc 0 N, vstate N d x * vstate N e x

theorem gram_eq_card (N d e : ℕ) :
    gram N d e = ((Hset N (Nat.lcm d e)).card : ℝ) /
      (Real.sqrt ((N / d : ℕ) : ℝ) * Real.sqrt ((N / e : ℕ) : ℝ)) := by
  unfold gram vstate
  have : ∀ x ∈ Ioc 0 N, (if d ∣ x then 1 / Real.sqrt ((N / d : ℕ) : ℝ) else 0) *
      (if e ∣ x then 1 / Real.sqrt ((N / e : ℕ) : ℝ) else 0) =
      if Nat.lcm d e ∣ x then 1 / (Real.sqrt ((N / d : ℕ) : ℝ) * Real.sqrt ((N / e : ℕ) : ℝ))
      else 0 := by
    intro x _
    by_cases hd : d ∣ x <;> by_cases he : e ∣ x <;> simp [hd, he, Nat.lcm_dvd_iff, one_div]; try ring
  rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [Hset]
  field_simp

/-- **The critical GCD kernel is the subgroup Gram matrix.** -/
theorem gram_eq (N d e : ℕ) (hN : 0 < N) (hd : 0 < d) (he : 0 < e) (hdN : d ∣ N) (heN : e ∣ N) :
    gram N d e = (Nat.gcd d e : ℝ) / Real.sqrt ((d : ℝ) * e) := by
  have hl : Nat.lcm d e ∣ N := Nat.lcm_dvd hdN heN
  have hl0 : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hg0 : 0 < Nat.gcd d e := Nat.gcd_pos_of_pos_left _ hd
  rw [gram_eq_card, card_Hset]
  have hgl : (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) = d * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have ca : ((N / d : ℕ) : ℝ) = N / d := Nat.cast_div hdN (by positivity)
  have cb : ((N / e : ℕ) : ℝ) = N / e := Nat.cast_div heN (by positivity)
  have cc : ((N / Nat.lcm d e : ℕ) : ℝ) = N / Nat.lcm d e := Nat.cast_div hl (by positivity)
  rw [ca, cb, cc, ← Real.sqrt_mul (by positivity)]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hlr : (0 : ℝ) < Nat.lcm d e := by exact_mod_cast hl0
  have hgr : (0 : ℝ) < Nat.gcd d e := by exact_mod_cast hg0
  rw [div_eq_div_iff (by positivity) (by positivity)]
  -- (N / l) * √(d e) = g * √((N/d)(N/e))
  have key : ((N : ℝ) / (Nat.lcm d e : ℝ)) ^ 2 * (d * e) =
      (Nat.gcd d e : ℝ) ^ 2 * (N / d * (N / e)) := by
    field_simp
    rw [show (d : ℝ) ^ 2 * (e : ℝ) ^ 2 = ((d : ℝ) * e) ^ 2 by ring, ← hgl]
    ring
  have h1 : ((N : ℝ) / (Nat.lcm d e : ℝ)) * Real.sqrt (d * e) =
      Real.sqrt (((N : ℝ) / (Nat.lcm d e : ℝ)) ^ 2 * (d * e)) := by
    rw [Real.sqrt_mul (sq_nonneg ((N : ℝ) / (Nat.lcm d e : ℝ))) (d * e),
      Real.sqrt_sq (by positivity)]
  have h2 : (Nat.gcd d e : ℝ) * Real.sqrt ((N : ℝ) / d * (N / e)) =
      Real.sqrt ((Nat.gcd d e : ℝ) ^ 2 * ((N : ℝ) / d * (N / e))) := by
    rw [Real.sqrt_mul (sq_nonneg (Nat.gcd d e : ℝ)) ((N : ℝ) / d * (N / e)),
      Real.sqrt_sq (by positivity)]
  rw [h1, h2, key]

/-- **The prime overlap is `p^{-1/2}`.** -/
theorem overlap_prime (N d p : ℕ) (hN : 0 < N) (hd : 0 < d) (hp : 0 < p) (hdN : d ∣ N) (hdpN : d * p ∣ N) :
    gram N d (d * p) = 1 / Real.sqrt p := by
  rw [gram_eq N d (d * p) hN hd (Nat.mul_pos hd hp) hdN hdpN]
  have hg : Nat.gcd d (d * p) = d := Nat.gcd_eq_left (dvd_mul_right d p)
  rw [hg]
  have : Real.sqrt ((d : ℝ) * ((d * p : ℕ) : ℝ)) = d * Real.sqrt p := by
    push_cast
    rw [show (d : ℝ) * (d * p) = (d : ℝ) ^ 2 * p by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
  rw [this]
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsr : Real.sqrt p ≠ 0 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp
    positivity
  field_simp

/-! ### The Möbius parity vector -/

/-- The squarefree-divisor kernel `K(d_T, d_S) = ∏_{p ∈ T △ S} w_p` (`w_p = p^{-1/2}`). -/
noncomputable def kern (w : ℕ → ℝ) (T S : Finset ℕ) : ℝ := ∏ p ∈ symmDiff T S, w p

theorem symmDiff_insert_left {q : ℕ} {T0 S : Finset ℕ} (hq0 : q ∉ T0) (hqS : q ∉ S) :
    symmDiff (insert q T0) S = insert q (symmDiff T0 S) := by
  ext x
  simp only [Finset.mem_symmDiff, mem_insert]
  by_cases hx : x = q <;> simp [hx, hq0, hqS]

theorem symmDiff_insert_right {q : ℕ} {T0 S : Finset ℕ} (hq0 : q ∉ T0) (hqS : q ∉ S) :
    symmDiff T0 (insert q S) = insert q (symmDiff T0 S) := by
  ext x
  simp only [Finset.mem_symmDiff, mem_insert]
  by_cases hx : x = q <;> simp [hx, hq0, hqS]

theorem symmDiff_insert_both {q : ℕ} {T0 S : Finset ℕ} (hq0 : q ∉ T0) (hqS : q ∉ S) :
    symmDiff (insert q T0) (insert q S) = symmDiff T0 S := by
  ext x
  simp only [Finset.mem_symmDiff, mem_insert]
  by_cases hx : x = q <;> simp [hx, hq0, hqS]

theorem q_notMem_symmDiff {q : ℕ} {P T S : Finset ℕ} (hqP : q ∉ P) (hT : T ⊆ P) (hS : S ⊆ P) :
    q ∉ symmDiff T S := by
  intro h
  rw [Finset.mem_symmDiff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact hqP (hT h1)
  · exact hqP (hS h1)

/-- **The Möbius parity vector is an eigenvector of the divisor kernel**, for arbitrary weights
`w_p`: `Σ_{S ⊆ P} (−1)^{|S|} ∏_{p ∈ T △ S} w_p = (−1)^{|T|} ∏_{p ∈ P} (1 − w_p)` for `T ⊆ P`. -/
theorem mobius_eigen_weighted (w : ℕ → ℝ) (P : Finset ℕ) :
    ∀ T ⊆ P, ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card * kern w T S =
      (-1 : ℝ) ^ T.card * ∏ p ∈ P, (1 - w p) := by
  induction P using Finset.induction_on with
  | empty =>
    intro T hT
    have : T = ∅ := Finset.subset_empty.mp hT
    subst this
    simp [kern]
  | insert q P hqP ih =>
    intro T hT
    set T0 := T.erase q with hT0
    have hT0P : T0 ⊆ P := by
      intro x hx
      have := hT (Finset.mem_of_mem_erase hx)
      rcases Finset.mem_insert.mp this with rfl | h
      · exact absurd rfl (Finset.ne_of_mem_erase hx)
      · exact h
    have hq0 : q ∉ T0 := Finset.notMem_erase q T
    rw [Finset.sum_powerset_insert hqP, Finset.prod_insert hqP]
    have step : ∀ S ∈ P.powerset, (-1 : ℝ) ^ S.card * kern w T S +
        (-1 : ℝ) ^ (insert q S).card * kern w T (insert q S) =
        (if q ∈ T then -(1 - w q) else (1 - w q)) * ((-1 : ℝ) ^ S.card * kern w T0 S) := by
      intro S hS
      have hSP : S ⊆ P := Finset.mem_powerset.mp hS
      have hqS : q ∉ S := fun h => hqP (hSP h)
      have hqn : q ∉ symmDiff T0 S := q_notMem_symmDiff hqP hT0P hSP
      rw [Finset.card_insert_of_notMem hqS]
      by_cases hqT : q ∈ T
      · have hTeq : T = insert q T0 := (Finset.insert_erase hqT).symm
        simp only [kern, hTeq, symmDiff_insert_left hq0 hqS, symmDiff_insert_both hq0 hqS,
          Finset.prod_insert hqn, Finset.mem_insert_self, if_true, pow_succ]
        ring
      · have hTeq : T = T0 := (Finset.erase_eq_of_notMem hqT).symm
        simp only [kern, hTeq, symmDiff_insert_right hq0 hqS, Finset.prod_insert hqn, hq0, if_false,
          pow_succ]
        ring
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl step, ← Finset.mul_sum,
      ih T0 hT0P]
    by_cases hqT : q ∈ T
    · have hc : T.card = T0.card + 1 := by
        rw [hT0, Finset.card_erase_of_mem hqT]
        have := Finset.card_pos.mpr ⟨q, hqT⟩
        omega
      simp [hqT, hc, pow_succ]
      ring
    · have hc : T.card = T0.card := by rw [hT0, Finset.erase_eq_of_notMem hqT]
      simp [hqT, hc]
      ring

/-- The eigenvalue statement for the critical weights `w_p = p^{-1/2}`. -/
theorem mobius_eigen (P : Finset ℕ) {T : Finset ℕ} (hT : T ⊆ P) :
    ∑ S ∈ P.powerset, (-1 : ℝ) ^ S.card * kern (fun p => 1 / Real.sqrt p) T S =
      (-1 : ℝ) ^ T.card * ∏ p ∈ P, (1 - 1 / Real.sqrt p) :=
  mobius_eigen_weighted _ P T hT

end GppSelfDualDivisor
