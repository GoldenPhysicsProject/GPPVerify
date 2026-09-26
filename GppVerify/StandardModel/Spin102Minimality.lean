import Mathlib.Tactic

/-!
# Signature arithmetic forcing the first real chiral completion

Starting from signature (6,2), add n positive-definite internal directions while
preserving the two timelike directions. The Majorana--Weyl congruence is

  p - q ≡ 0 (mod 8).

Hence

  (6+n) - 2 = 4+n ≡ 0 (mod 8),

so n ≡ 4 (mod 8). The first solution is n=4 and the next is n=12.
Therefore the (10,2) completion is the unique such completion of total
dimension strictly below 20.

This file formalizes only the elementary congruence/minimality arithmetic.
The Clifford-classification premise itself is external standard input.
-/

namespace GppSpin102Minimality

/-- Signature difference after adding n positive internal directions to (6,2). -/
def signatureDifference (n : ℕ) : ℕ := 4 + n

/-- Arithmetic form of the Majorana--Weyl congruence for the positive extension. -/
def mwCongruence (n : ℕ) : Prop := signatureDifference n % 8 = 0

/-- Four added positive directions satisfy the congruence. -/
theorem four_is_mw : mwCongruence 4 := by
  norm_num [mwCongruence, signatureDifference]

/-- Twelve added positive directions are the next displayed solution. -/
theorem twelve_is_mw : mwCongruence 12 := by
  norm_num [mwCongruence, signatureDifference]

/-- No positive extension smaller than four can satisfy the congruence. -/
theorem no_mw_below_four (n : ℕ) (hn : n < 4) :
    ¬ mwCongruence n := by
  intro h
  unfold mwCongruence signatureDifference at h
  omega

/-- Any solution strictly between four and twelve is impossible. -/
theorem no_mw_strictly_between_four_and_twelve
    (n : ℕ) (h4 : 4 < n) (h12 : n < 12) :
    ¬ mwCongruence n := by
  intro h
  unfold mwCongruence signatureDifference at h
  omega

/-- The first positive extension satisfying the Majorana--Weyl congruence is exactly four. -/
theorem first_mw_extension
    (n : ℕ) (h : mwCongruence n) (hn : n < 12) :
    n = 4 := by
  unfold mwCongruence signatureDifference at h
  omega

/-- Since the original parent has dimension eight, total dimension below twenty
forces the unique Majorana--Weyl-compatible positive extension to be (10,2). -/
theorem unique_mw_completion_below_twenty
    (n : ℕ) (h : mwCongruence n) (hdim : 8 + n < 20) :
    n = 4 := by
  apply first_mw_extension n h
  omega

/-- Any later positive extension has at least twelve extra directions, hence total
dimension at least twenty. -/
theorem next_mw_extension_at_least_twelve
    (n : ℕ) (h : mwCongruence n) (hne : n ≠ 4) :
    12 ≤ n := by
  by_contra hlt
  have hn : n < 12 := by omega
  have hn4 : n = 4 := first_mw_extension n h hn
  exact hne hn4

end GppSpin102Minimality
