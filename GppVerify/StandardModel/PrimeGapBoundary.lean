import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# The exceptional low-prime additive cluster 2--3--5--7

This file proves the elementary arithmetic facts used before any Lie-theoretic
interpretation:

* two consecutive primes must be 2 and 3;
* a triple p,p+2,p+4 of primes must be 3,5,7;
* hence there is no four-prime chain with every gap equal to 2;
* there is no prime one or two steps above 7.

The mod-3 obstruction is the whole reason that 3--5--7 is the unique overlap of
two twin-prime edges.

No gauge-theory or particle-physics identification is made here.
-/

namespace GppPrimeGapBoundary

/-- Among n,n+2,n+4, one is divisible by 3. -/
theorem one_of_three_gap_two_mod_three (n : ℕ) :
    n % 3 = 0 ∨ (n + 2) % 3 = 0 ∨ (n + 4) % 3 = 0 := by
  omega

/-- Two consecutive primes are necessarily 2 and 3. -/
theorem consecutive_primes_unique {p : ℕ}
    (hp : p.Prime) (hp1 : (p + 1).Prime) :
    p = 2 ∧ p + 1 = 3 := by
  have hp_eq : p = 2 := by
    rcases hp.eq_two_or_odd with h2 | hodd
    · exact h2
    · have hmod : (p + 1) % 2 = 0 := by omega
      have hd : 2 ∣ p + 1 := Nat.dvd_of_mod_eq_zero hmod
      have heq : p + 1 = 2 :=
        (hp1.dvd_iff_eq (by norm_num : (2 : ℕ) ≠ 1)).mp hd
      have hp2 : 2 ≤ p := hp.two_le
      omega
  omega

/-- The only prime triple with consecutive gap 2 is 3,5,7. -/
theorem gap_two_prime_triple_unique {p : ℕ}
    (hp : p.Prime) (hp2 : (p + 2).Prime) (hp4 : (p + 4).Prime) :
    p = 3 ∧ p + 2 = 5 ∧ p + 4 = 7 := by
  have hres := one_of_three_gap_two_mod_three p
  have hp_eq : p = 3 := by
    rcases hres with h0 | h2 | h4
    · have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp hd
    · have hd : 3 ∣ p + 2 := Nat.dvd_of_mod_eq_zero h2
      have heq : p + 2 = 3 :=
        (hp2.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp hd
      have hp_lower : 2 ≤ p := hp.two_le
      omega
    · have hd : 3 ∣ p + 4 := Nat.dvd_of_mod_eq_zero h4
      have heq : p + 4 = 3 :=
        (hp4.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).mp hd
      omega
  omega

/-- There cannot be four primes p,p+2,p+4,p+6. -/
theorem no_four_prime_gap_two_chain (p : ℕ) :
    ¬(p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime ∧ (p + 6).Prime) := by
  rintro ⟨hp, hp2, hp4, hp6⟩
  have h := gap_two_prime_triple_unique hp hp2 hp4
  have hp3 : p = 3 := h.1
  subst p
  norm_num at hp6

/-- The low minimal-gap chain stops at 7: neither 8 nor 9 is prime. -/
theorem no_prime_one_or_two_above_seven {q : ℕ}
    (hlo : 7 < q) (hhi : q ≤ 9) :
    ¬q.Prime := by
  interval_cases q <;> norm_num

/-- The four displayed boundary vertices are indeed prime. -/
theorem boundary_vertices_prime :
    Nat.Prime 2 ∧ Nat.Prime 3 ∧ Nat.Prime 5 ∧ Nat.Prime 7 := by
  norm_num

end GppPrimeGapBoundary

#print axioms GppPrimeGapBoundary.consecutive_primes_unique
#print axioms GppPrimeGapBoundary.gap_two_prime_triple_unique
#print axioms GppPrimeGapBoundary.no_four_prime_gap_two_chain
