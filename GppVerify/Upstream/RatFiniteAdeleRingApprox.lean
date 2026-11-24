/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin (with AI assistance from Claude Code)
-/
import GppVerify.Upstream.RatFiniteAdeleRingHaar

/-!
# Strong approximation for `ℚ` in the finite adeles

Mathlib-only, in Mathlib's naming, for upstreaming (it uses only `Rat.FiniteAdeleRing.integralAdeles`
from `RatFiniteAdeleRingHaar.lean`).

* `Rat.FiniteAdeleRing.exists_rat_sub_mem_integralAdeles` (**strong approximation**): every finite
  adele is a rational plus an everywhere-integral adele. Locally, every `x ∈ ℚ_p` is within `ℤ_p` of
  some `m / p^k` (`exists_rat_sub_norm_le_one`), which is integral at every other prime; the global
  statement follows by induction on the finitely many non-integral places.
* `Rat.FiniteAdeleRing.den_eq_one_of_forall_mem_adicCompletionIntegers`: a rational that is integral
  at every place is an integer.
-/

open IsDedekindDomain Rat.HeightOneSpectrum

namespace Rat.FiniteAdeleRing

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- Clearing a `p`-power denominator: `p^k x` is integral for some `k`. -/
theorem exists_pow_mul_norm_le_one (p : ℕ) [hp : Fact p.Prime] (x : ℚ_[p]) :
    ∃ k : ℕ, ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  refine ⟨(-x.valuation).toNat, ?_⟩
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  rw [norm_mul, norm_pow, Padic.norm_p, Padic.norm_eq_zpow_neg_valuation hx, inv_pow,
    ← zpow_natCast, ← zpow_neg, ← zpow_add₀ (by positivity)]
  apply zpow_le_one_of_nonpos₀ hp1.le
  have := Int.self_le_toNat (-x.valuation)
  omega

/-- **Local approximation.** Every `x ∈ ℚ_p` is within `ℤ_p` of a rational `m / p^k`. -/
theorem exists_rat_sub_norm_le_one (p : ℕ) [hp : Fact p.Prime] (x : ℚ_[p]) :
    ∃ (m : ℤ) (k : ℕ), ‖x - ((m / (p : ℚ) ^ k : ℚ) : ℚ_[p])‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_pow_mul_norm_le_one p x
  set y : ℤ_[p] := ⟨(p : ℚ_[p]) ^ k * x, hk⟩
  refine ⟨(y.appr k : ℤ), k, ?_⟩
  have hspec := (PadicInt.norm_le_pow_iff_mem_span_pow _ k).2 (PadicInt.appr_spec k y)
  have hpk : (p : ℚ_[p]) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.out.ne_zero)
  have hpn : ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-(k : ℤ)) := by
    rw [norm_pow, Padic.norm_p, inv_pow, zpow_neg, zpow_natCast]
  have hy : ((y : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * x := rfl
  have e : x - ((((y.appr k : ℤ) : ℚ) / (p : ℚ) ^ k : ℚ) : ℚ_[p]) =
      ((p : ℚ_[p]) ^ k)⁻¹ * (((y - (y.appr k : ℤ_[p]) : ℤ_[p])) : ℚ_[p]) := by
    rw [PadicInt.coe_sub, hy]
    push_cast
    field_simp
  rw [e, norm_mul, norm_inv, hpn]
  have : ‖(((y - (y.appr k : ℤ_[p]) : ℤ_[p])) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := hspec
  have hpos : (0 : ℝ) < (p : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast hp.out.pos) _
  calc ((p : ℝ) ^ (-(k : ℤ)))⁻¹ * _ ≤ ((p : ℝ) ^ (-(k : ℤ)))⁻¹ * (p : ℝ) ^ (-(k : ℤ)) := by
        gcongr
    _ = 1 := inv_mul_cancel₀ hpos.ne'

/-- `m / p^k` is integral at every prime `ℓ ≠ p`. -/
theorem padicNorm_div_pow_le_one {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] (h : ℓ ≠ p)
    (m : ℤ) (k : ℕ) : padicNorm ℓ (m / (p : ℚ) ^ k) ≤ 1 := by
  have hpow : ∀ k : ℕ, padicNorm ℓ ((p : ℚ) ^ k) = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ n ih => rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_of_prime_of_ne h, one_mul]
  rw [padicNorm.div, hpow, div_one]
  exact padicNorm.of_int m

variable (v : HeightOneSpectrum ℤ)

theorem padicEquiv_algebraMap (q : ℚ) :
    adicCompletion.padicEquiv v (algebraMap ℚ (v.adicCompletion ℚ) q) =
      (q : ℚ_[(primesEquiv v : ℕ)]) := by
  simp only [eq_ratCast, map_ratCast]

/-- A rational is integral at `v` iff its `p`-adic norm is at most one, `p` the prime of `v`. -/
theorem algebraMap_mem_adicCompletionIntegers_iff (q : ℚ) :
    algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ ↔
      padicNorm (primesEquiv v : ℕ) q ≤ 1 := by
  rw [mem_adicCompletionIntegers_iff, padicEquiv_algebraMap, Padic.eq_padicNorm]
  rw [← Rat.cast_one (α := ℝ), Rat.cast_le]

theorem intCast_mem_adicCompletionIntegers (n : ℤ) :
    algebraMap ℚ (v.adicCompletion ℚ) n ∈ v.adicCompletionIntegers ℚ :=
  (algebraMap_mem_adicCompletionIntegers_iff v n).2 (padicNorm.of_int n)

variable {v}

/-- A rational that is `p`-integral for every prime `p` is an integer. -/
theorem den_eq_one_of_padicNorm_le_one (q : ℚ)
    (h : ∀ p : ℕ, p.Prime → padicNorm p q ≤ 1) : q.den = 1 := by
  by_contra hden
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
  have : Fact p.Prime := ⟨hp⟩
  have hq : q ≠ 0 := by rintro rfl; simp at hden
  have hnum : ¬ (p : ℤ) ∣ q.num := by
    intro hn
    have h1 : p ∣ q.num.natAbs := Int.natCast_dvd.mp hn
    exact hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h1 q.reduced).eq_one_of_dvd hpd)
  have hv : padicValRat p q ≤ -1 := by
    have hden1 : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd q.den_ne_zero hpd
    rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum]
    omega
  have hn := padicNorm.eq_zpow_of_nonzero (p := p) hq
  have hp1 : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have : (1 : ℚ) < padicNorm p q := by
    rw [hn]
    calc (1 : ℚ) < (p : ℚ) ^ (1 : ℤ) := by simpa using hp1
      _ ≤ (p : ℚ) ^ (-padicValRat p q) := zpow_le_zpow_right₀ hp1.le (by omega)
  exact absurd (h p hp) (not_le.mpr this)

/-- A rational integral at every place is an integer. -/
theorem den_eq_one_of_forall_mem_adicCompletionIntegers (q : ℚ)
    (h : ∀ v : HeightOneSpectrum ℤ,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ) : q.den = 1 :=
  den_eq_one_of_padicNorm_le_one q fun p hp => by
    obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum ℤ, (primesEquiv w : ℕ) = p :=
      ⟨(primesEquiv (R := ℤ)).symm ⟨p, hp⟩,
        congrArg Subtype.val ((primesEquiv (R := ℤ)).apply_symm_apply ⟨p, hp⟩)⟩
    rw [← hw]
    exact (algebraMap_mem_adicCompletionIntegers_iff w q).1 (h w)

/-- A rational integral at every place equals its numerator. -/
theorem eq_num_of_forall_mem_adicCompletionIntegers (q : ℚ)
    (h : ∀ v : HeightOneSpectrum ℤ,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ) : q = q.num := by
  have hd := den_eq_one_of_forall_mem_adicCompletionIntegers q h
  rw [← Rat.num_div_den q]; simp [hd]

open Classical in
/-- **Strong approximation for `ℚ`.** Every finite adele is a rational plus an adele that is
integral at every place. -/
theorem exists_rat_sub_mem_integralAdeles (f : FiniteAdeleRing ℤ ℚ) :
    ∃ q : ℚ, ∀ v, f v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  have hfin : {v : HeightOneSpectrum ℤ | f v ∉ v.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.1 f.2
  suffices H : ∀ T : Finset (HeightOneSpectrum ℤ), ∀ f : FiniteAdeleRing ℤ ℚ,
      {v : HeightOneSpectrum ℤ | f v ∉ v.adicCompletionIntegers ℚ} ⊆ T →
      ∃ q : ℚ, ∀ v, f v - algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ from
    H hfin.toFinset f (by simp)
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨0, fun v => ?_⟩
    have : v ∉ {v : HeightOneSpectrum ℤ | f v ∉ v.adicCompletionIntegers ℚ} :=
      fun hv => by simpa using hf hv
    simpa using this
  | insert v₀ T hv₀ ih =>
    intro f hf
    obtain ⟨m, k, hmk⟩ := exists_rat_sub_norm_le_one (primesEquiv v₀ : ℕ)
      (adicCompletion.padicEquiv v₀ (f v₀))
    set q₀ : ℚ := m / ((primesEquiv v₀ : ℕ) : ℚ) ^ k
    set f' : FiniteAdeleRing ℤ ℚ := f - algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q₀
    have hf' : ∀ v, f' v = f v - algebraMap ℚ (v.adicCompletion ℚ) q₀ := fun v => rfl
    have hsub : {v : HeightOneSpectrum ℤ | f' v ∉ v.adicCompletionIntegers ℚ} ⊆ T := by
      intro v hv
      simp only [Set.mem_ofPred_eq, hf'] at hv
      by_cases hvv : v = v₀
      · subst hvv
        exfalso; apply hv
        rw [mem_adicCompletionIntegers_iff, map_sub, padicEquiv_algebraMap]
        exact hmk
      · have hq : algebraMap ℚ (v.adicCompletion ℚ) q₀ ∈ v.adicCompletionIntegers ℚ :=
          (algebraMap_mem_adicCompletionIntegers_iff v q₀).2
            (padicNorm_div_pow_le_one
              (fun h => hvv (primesEquiv.injective (Subtype.ext h))) m k)
        have hfv : v ∈ {v : HeightOneSpectrum ℤ | f v ∉ v.adicCompletionIntegers ℚ} := by
          intro hint; exact hv ((v.adicCompletionIntegers ℚ).sub_mem hint hq)
        have := hf hfv
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
        exact this.resolve_left hvv
    obtain ⟨q₁, hq₁⟩ := ih f' hsub
    refine ⟨q₀ + q₁, fun v => ?_⟩
    have := hq₁ v
    rw [hf'] at this
    rw [map_add]
    convert this using 1
    ring

/-- Strong approximation, in the form used for the fundamental domain. -/
theorem exists_rat_sub_mem_integralAdeles' (f : FiniteAdeleRing ℤ ℚ) :
    ∃ q : ℚ, f - algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q ∈ integralAdeles :=
  (exists_rat_sub_mem_integralAdeles f).imp fun _ h v => h v

end Rat.FiniteAdeleRing
