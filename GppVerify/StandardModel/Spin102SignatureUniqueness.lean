import Mathlib.Tactic

/-!
# Signature arithmetic behind the (10,2) completion

For a real chiral Majorana--Weyl structure one uses the standard real-Clifford
congruence p-q ≡ 0 (mod 8).  This file formalizes only the arithmetic consequence
for the orientation parent

    (6,2) -> (6+n,2)

obtained by adjoining n positive directions.

The starting signature has p-q=4, so the congruence becomes

    4+n ≡ 0 (mod 8),

equivalently n ≡ 4 (mod 8).

Therefore n=4, giving (10,2), is the unique admissible positive extension with
total dimension below 20.  The next arithmetic possibility is n=12, giving (18,2).

The Clifford-theoretic Majorana--Weyl classification itself is standard prior art
and is not re-proved here.
-/

namespace GppSpin102SignatureUniqueness

/-- Residue condition inherited from the standard MW criterion for (6+n,2). -/
def mwResidue (n : ℕ) : Prop := (4 + n) % 8 = 0

theorem n4_satisfies : mwResidue 4 := by
  norm_num [mwResidue]

theorem n12_satisfies : mwResidue 12 := by
  norm_num [mwResidue]

/-- Below n=12, the only positive extension satisfying the MW residue is n=4. -/
theorem unique_extension_below_twelve
    {n : ℕ} (hn : n < 12) (hMW : mwResidue n) :
    n = 4 := by
  unfold mwResidue at hMW
  omega

/-- Equivalently: below total dimension 20, (10,2) is the unique candidate. -/
theorem unique_total_dimension_below_twenty
    {n : ℕ} (hdim : 8 + n < 20) (hMW : mwResidue n) :
    n = 4 ∧ 8 + n = 12 := by
  have hn : n < 12 := by omega
  have h4 : n = 4 := unique_extension_below_twelve hn hMW
  subst n
  norm_num

/-- Any admissible positive extension strictly larger than n=4 has n at least 12. -/
theorem next_extension_at_least_twelve
    {n : ℕ} (h4 : 4 < n) (hMW : mwResidue n) :
    12 ≤ n := by
  unfold mwResidue at hMW
  omega

/-- Hence the next admissible total dimension after 12 is at least 20. -/
theorem next_total_dimension_at_least_twenty
    {n : ℕ} (h4 : 4 < n) (hMW : mwResidue n) :
    20 ≤ 8 + n := by
  have hn : 12 ≤ n := next_extension_at_least_twelve h4 hMW
  omega

end GppSpin102SignatureUniqueness

#print axioms GppSpin102SignatureUniqueness.unique_total_dimension_below_twenty
#print axioms GppSpin102SignatureUniqueness.next_total_dimension_at_least_twenty
