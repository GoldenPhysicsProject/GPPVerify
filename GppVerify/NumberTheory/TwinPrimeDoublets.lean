import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Twin primes decompose into singlets and doublets, with one exceptional triplet

Regard primes as vertices and join two vertices when their difference is `2`.  The graph
has an elementary but suggestive exact structure:

* a prime greater than `5` cannot have neighbors on both sides;
* hence every such vertex is either an isolated singlet or belongs to exactly one
  one-sided twin doublet;
* the only overlapping twin pairs are `(3,5)` and `(5,7)`, with center `5`.

The reason is reduction modulo `3`: among `p-2`, `p`, and `p+2`, one is divisible by `3`.
If all three are prime, that divisible member must itself be `3`, forcing the exceptional
triplet.

This finite theorem does not prove that infinitely many twin doublets exist (the twin-prime
conjecture remains open), nor does it identify the doublets with a physical `SU(2)`
representation.  It does justify treating gap-2 correlations as a genuine two-prime sector
on top of the one-prime Euler factors.
-/

namespace GppTwinPrime

/-- The center of any three-prime gap-2 chain is `5`. -/
theorem twin_triplet_center_eq_five {p : ℕ} (hp : p.Prime)
    (hleft : (p - 2).Prime) (hright : (p + 2).Prime) :
    p = 5 := by
  have hp2 : 2 ≤ p := hp.two_le
  have hmodlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hcases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · have hdiv : 3 ∣ p := Nat.dvd_iff_mod_eq_zero.mpr h0
    have hp3 : p = 3 := (hp.dvd_iff_eq (by norm_num)).mp hdiv
    subst p
    norm_num at hleft
  · have hmodplus : (p + 2) % 3 = 0 := by omega
    have hdiv : 3 ∣ p + 2 := Nat.dvd_iff_mod_eq_zero.mpr hmodplus
    have heq : p + 2 = 3 := (hright.dvd_iff_eq (by norm_num)).mp hdiv
    omega
  · have hmodminus : (p - 2) % 3 = 0 := by omega
    have hdiv : 3 ∣ p - 2 := Nat.dvd_iff_mod_eq_zero.mpr hmodminus
    have heq : p - 2 = 3 := (hleft.dvd_iff_eq (by norm_num)).mp hdiv
    omega

/-- Every prime above `5` has at most one gap-2 direction. -/
theorem prime_gt_five_not_two_sided_twin {p : ℕ} (hp : p.Prime) (hp5 : 5 < p) :
    ¬((p - 2).Prime ∧ (p + 2).Prime) := by
  rintro ⟨hleft, hright⟩
  have := twin_triplet_center_eq_five hp hleft hright
  omega

/-- `5` is the unique prime center with prime neighbors at distance `2`. -/
theorem two_sided_twin_iff_five {p : ℕ} (hp : p.Prime) :
    (p - 2).Prime ∧ (p + 2).Prime ↔ p = 5 := by
  constructor
  · rintro ⟨hleft, hright⟩
    exact twin_triplet_center_eq_five hp hleft hright
  · rintro rfl
    norm_num

/-- Exact singlet/doublet classification above the exceptional triplet: neither neighbor
is prime, only the lower neighbor is prime, or only the upper neighbor is prime. -/
theorem prime_gt_five_singlet_or_one_sided_doublet {p : ℕ}
    (hp : p.Prime) (hp5 : 5 < p) :
    (¬(p - 2).Prime ∧ ¬(p + 2).Prime) ∨
      ((p - 2).Prime ∧ ¬(p + 2).Prime) ∨
      (¬(p - 2).Prime ∧ (p + 2).Prime) := by
  have hnotboth := prime_gt_five_not_two_sided_twin hp hp5
  by_cases hleft : (p - 2).Prime
  · right
    left
    exact ⟨hleft, fun hright => hnotboth ⟨hleft, hright⟩⟩
  · by_cases hright : (p + 2).Prime
    · exact Or.inr (Or.inr ⟨hleft, hright⟩)
    · exact Or.inl ⟨hleft, hright⟩

end GppTwinPrime
